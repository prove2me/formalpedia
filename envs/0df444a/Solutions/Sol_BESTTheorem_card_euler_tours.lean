-- Prove2me | solution 1 for BESTTheorem.card_euler_tours
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-12T04:46:56.1299+00:00
-- url     : https://prove2.me/submissions/6fe881b5-683d-49b6-8985-3342939b0d0f

import Mathlib

open Finset

set_option linter.unusedSectionVars false

namespace BESTAux

variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]

abbrev Out (tl : A → V) (v : V) := {a : A // tl a = v}

def dg (tl : A → V) (v : V) : ℕ := Fintype.card (Out tl v)

abbrev Ords (tl : A → V) := ∀ v : V, Fin (dg tl v) ≃ Out tl v

def rk {tl : A → V} (O : Ords tl) (a : A) : ℕ := ((O (tl a)).symm ⟨a, rfl⟩).val

lemma rk_eq {tl : A → V} (O : Ords tl) {a : A} {v : V} (h : tl a = v) :
    rk O a = ((O v).symm ⟨a, h⟩).val := by
  subst h; rfl

lemma rk_O {tl : A → V} (O : Ords tl) (v : V) (i : Fin (dg tl v)) :
    rk O (O v i).1 = i.val := by
  rw [rk_eq O (O v i).2]; simp

lemma rk_lt {tl : A → V} (O : Ords tl) (a : A) : rk O a < dg tl (tl a) :=
  ((O (tl a)).symm _).isLt

def step (tl hd : A → V) (O : Ords tl) (s : V × (V → ℕ)) : V × (V → ℕ) :=
  if h : s.2 s.1 < dg tl s.1 then
    (hd (O s.1 ⟨s.2 s.1, h⟩).1, Function.update s.2 s.1 (s.2 s.1 + 1))
  else s

def st (tl hd : A → V) (O : Ords tl) (r : V) : ℕ → V × (V → ℕ)
  | 0 => (r, 0)
  | t + 1 => step tl hd O (st tl hd O r t)

def arcAt (tl hd : A → V) (O : Ords tl) (r : V) (e : A) (t : ℕ) : A :=
  if h : (st tl hd O r t).2 (st tl hd O r t).1 < dg tl (st tl hd O r t).1 then
    (O _ ⟨_, h⟩).1 else e

def outCnt (tl hd : A → V) (O : Ords tl) (r : V) (e : A) (t : ℕ) (w : V) : ℕ :=
  ∑ s ∈ range t, if tl (arcAt tl hd O r e s) = w then 1 else 0

def inCnt (tl hd : A → V) (O : Ords tl) (r : V) (e : A) (t : ℕ) (w : V) : ℕ :=
  ∑ s ∈ range t, if hd (arcAt tl hd O r e s) = w then 1 else 0

/-- the walk is not stuck at any time before `t` -/
def NS (tl hd : A → V) (O : Ords tl) (r : V) (t : ℕ) : Prop :=
  ∀ s < t, (st tl hd O r s).2 (st tl hd O r s).1 < dg tl (st tl hd O r s).1

section
variable {tl hd : A → V} (O : Ords tl) (r : V) (e : A)

lemma tl_arcAt {t : ℕ} (h : (st tl hd O r t).2 (st tl hd O r t).1 < dg tl (st tl hd O r t).1) :
    tl (arcAt tl hd O r e t) = (st tl hd O r t).1 := by
  unfold arcAt; rw [dif_pos h]; exact (O _ _).2

lemma rk_arcAt {t : ℕ} (h : (st tl hd O r t).2 (st tl hd O r t).1 < dg tl (st tl hd O r t).1) :
    rk O (arcAt tl hd O r e t) = (st tl hd O r t).2 (st tl hd O r t).1 := by
  unfold arcAt; rw [dif_pos h, rk_O]

lemma st_succ {t : ℕ} (h : (st tl hd O r t).2 (st tl hd O r t).1 < dg tl (st tl hd O r t).1) :
    st tl hd O r (t + 1) = (hd (arcAt tl hd O r e t),
      Function.update (st tl hd O r t).2 (st tl hd O r t).1
        ((st tl hd O r t).2 (st tl hd O r t).1 + 1)) := by
  show step tl hd O (st tl hd O r t) = _
  unfold step arcAt; rw [dif_pos h, dif_pos h]

lemma inv (t : ℕ) (hNS : NS tl hd O r t) :
    (st tl hd O r t).2 = outCnt tl hd O r e t ∧
    ∀ w, inCnt tl hd O r e t w + (if w = r then 1 else 0) =
      outCnt tl hd O r e t w + (if w = (st tl hd O r t).1 then 1 else 0) := by
  induction t with
  | zero =>
    refine ⟨?_, fun w => ?_⟩
    · funext w; simp [st, outCnt]
    · simp only [st, outCnt, inCnt, range_zero, sum_empty, zero_add]
      split_ifs <;> simp_all
  | succ t ih =>
    have hNS' : NS tl hd O r t := fun s hs => hNS s (by omega)
    obtain ⟨ih1, ih2⟩ := ih hNS'
    have h := hNS t (by omega)
    rw [st_succ O r e h]
    have htl := tl_arcAt O r e h
    refine ⟨?_, fun w => ?_⟩
    · funext w
      simp only [outCnt, sum_range_succ]
      rw [← outCnt, ← ih1, htl]
      by_cases hw : w = (st tl hd O r t).1
      · subst hw; simp
      · rw [Function.update_of_ne hw]; simp [Ne.symm hw]
    · simp only [outCnt, inCnt, sum_range_succ]
      rw [← outCnt, ← inCnt, htl]
      have := ih2 w
      generalize inCnt tl hd O r e t w = I at this ⊢
      generalize outCnt tl hd O r e t w = J at this ⊢
      by_cases h1 : hd (arcAt tl hd O r e t) = w
      · by_cases h2 : (st tl hd O r t).1 = w
        · simp only [h1, h2, if_true] at this ⊢; split_ifs at this ⊢ <;> omega
        · simp only [h1, h2, if_true, if_false] at this ⊢; split_ifs at this ⊢ <;> simp_all <;> omega
      · by_cases h2 : (st tl hd O r t).1 = w
        · simp only [h1, h2, if_true, if_false] at this ⊢; split_ifs at this ⊢ <;> simp_all <;> omega
        · simp only [h1, h2, if_false] at this ⊢; split_ifs at this ⊢ <;> simp_all <;> omega

lemma outCnt_mono {s t : ℕ} (hst : s ≤ t) (w : V) :
    outCnt tl hd O r e s w ≤ outCnt tl hd O r e t w :=
  sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hst) (fun _ _ _ => Nat.zero_le _)

lemma outCnt_lt {s t : ℕ} (hst : s < t) :
    outCnt tl hd O r e s (tl (arcAt tl hd O r e s)) + 1 ≤
      outCnt tl hd O r e t (tl (arcAt tl hd O r e s)) := by
  have h1 : outCnt tl hd O r e (s + 1) (tl (arcAt tl hd O r e s)) =
      outCnt tl hd O r e s (tl (arcAt tl hd O r e s)) + 1 := by
    simp only [outCnt, sum_range_succ, if_true]
  rw [← h1]; exact outCnt_mono O r e hst _

lemma NS_mono {s t : ℕ} (hst : s ≤ t) (h : NS tl hd O r t) : NS tl hd O r s :=
  fun u hu => h u (by omega)

lemma rk_arcAt' {s : ℕ} (h : NS tl hd O r (s + 1)) :
    rk O (arcAt tl hd O r e s) = outCnt tl hd O r e s (tl (arcAt tl hd O r e s)) := by
  have hs := h s (by omega)
  rw [rk_arcAt O r e hs, tl_arcAt O r e hs, (inv O r e s (NS_mono O r (by omega) h)).1]

lemma rk_used {s t : ℕ} (hst : s < t) (h : NS tl hd O r t) :
    rk O (arcAt tl hd O r e s) + 1 ≤ outCnt tl hd O r e t (tl (arcAt tl hd O r e s)) := by
  rw [rk_arcAt' O r e (NS_mono O r (by omega) h)]; exact outCnt_lt O r e hst

lemma arcAt_inj {t : ℕ} (h : NS tl hd O r t) {s₁ s₂ : ℕ} (h₁ : s₁ < t) (h₂ : s₂ < t)
    (heq : arcAt tl hd O r e s₁ = arcAt tl hd O r e s₂) : s₁ = s₂ := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have a1 := rk_used O r e hlt (NS_mono O r (by omega) h)
    have a2 := rk_arcAt' O r e (s := s₂) (NS_mono O r (by omega) h)
    rw [heq] at a1; omega
  · have a1 := rk_used O r e hlt (NS_mono O r (by omega) h)
    have a2 := rk_arcAt' O r e (s := s₁) (NS_mono O r (by omega) h)
    rw [← heq] at a1; omega

lemma cnt_le {t : ℕ} (h : NS tl hd O r t) (P : A → Prop) [DecidablePred P] (B : Finset A)
    (hB : ∀ s < t, P (arcAt tl hd O r e s) → arcAt tl hd O r e s ∈ B) :
    (∑ s ∈ range t, if P (arcAt tl hd O r e s) then 1 else 0) ≤ B.card := by
  rw [sum_boole]
  simp only [Nat.cast_id]
  apply card_le_card_of_injOn (arcAt tl hd O r e)
  · intro s hs
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
    exact hB s hs.1 hs.2
  · intro s₁ hs₁ s₂ hs₂ heq
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs₁ hs₂
    exact arcAt_inj O r e h hs₁.1 hs₂.1 heq

lemma sum_outCnt (t : ℕ) : ∑ w, outCnt tl hd O r e t w = t := by
  unfold outCnt
  rw [sum_comm]
  simp

lemma card_eq_sum_dg (tl : A → V) : Fintype.card A = ∑ w, dg tl w := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := tl) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun w _ => ?_
  rw [dg, Fintype.card_subtype]

end

/-- parent of `v` in the last-exit forest of the orderings `O` -/
def pO {tl : A → V} (hd : A → V) (O : Ords tl) (r : V) (v : V) : V :=
  if h : 0 < dg tl v ∧ v ≠ r then hd (O v ⟨dg tl v - 1, by omega⟩).1 else v

/-- every vertex with an out-arc reaches the root `r` along `p` -/
def GT (tl : A → V) (r : V) (p : V → V) : Prop :=
  ∀ v, 0 < dg tl v → v ≠ r → ∃ k, p^[k] v = r

section
variable {tl hd : A → V} (O : Ords tl) (r : V) (e : A)

include e in
lemma not_stuck (hbal : ∀ w, (univ.filter (fun a => hd a = w)).card = dg tl w)
    (htree : GT tl r (pO hd O r)) {t : ℕ} (ht : t < Fintype.card A) (hNS : NS tl hd O r t) :
    (st tl hd O r t).2 (st tl hd O r t).1 < dg tl (st tl hd O r t).1 := by
  by_contra hst
  obtain ⟨hc, hflow⟩ := inv O r e t hNS
  set x := (st tl hd O r t).1 with hx
  have hin : ∀ w, inCnt tl hd O r e t w ≤ dg tl w := fun w => by
    rw [← hbal w]
    exact cnt_le O r e hNS (fun a => hd a = w) _ (fun s _ hs => by simp [hs])
  -- the walk is stuck at the root
  have hxr : x = r := by
    have h1 := hflow x
    have h2 := hin x
    rw [← hc, if_pos rfl] at h1
    by_contra hne
    rw [if_neg hne] at h1
    push Not at hst
    omega
  rw [hxr] at hst hflow
  have hcw : ∀ w, (st tl hd O r t).2 w = inCnt tl hd O r e t w := fun w => by
    have := hflow w
    rw [← hc] at this
    omega
  -- some vertex still has unused out-arcs
  obtain ⟨w, hw⟩ : ∃ w, (st tl hd O r t).2 w < dg tl w := by
    by_contra hall
    push Not at hall
    have h1 := sum_le_sum (fun w (_ : w ∈ univ) => hall w)
    rw [← card_eq_sum_dg, hc, sum_outCnt] at h1
    omega
  -- the set of such vertices is closed under the parent map
  have hclosed : ∀ u, (st tl hd O r t).2 u < dg tl u →
      (st tl hd O r t).2 (pO hd O r u) < dg tl (pO hd O r u) := by
    intro u hu
    have hur : u ≠ r := fun h => by rw [h] at hu; exact hst hu
    have hpos : 0 < dg tl u := by omega
    have hp : pO hd O r u = hd (O u ⟨dg tl u - 1, by omega⟩).1 := by
      unfold pO; rw [dif_pos ⟨hpos, hur⟩]
    set ℓ := (O u ⟨dg tl u - 1, by omega⟩).1 with hℓ
    have hrkℓ : rk O ℓ = dg tl u - 1 := rk_O O u _
    have htlℓ : tl ℓ = u := (O u _).2
    have hunused : ∀ s < t, arcAt tl hd O r e s ≠ ℓ := by
      intro s hs heq
      have := rk_used O r e hs hNS
      rw [heq, hrkℓ, htlℓ, ← hc] at this
      omega
    rw [hp, hcw]
    have := cnt_le O r e hNS (fun a => hd a = hd ℓ)
      ((univ.filter (fun a => hd a = hd ℓ)).erase ℓ)
      (fun s hs h' => by simp [h', hunused s hs])
    rw [card_erase_of_mem (by simp), hbal] at this
    have hpos' : 0 < dg tl (hd ℓ) := by
      rw [← hbal]; exact card_pos.mpr ⟨ℓ, by simp⟩
    unfold inCnt; omega
  have hwr : w ≠ r := fun h => by rw [h] at hw; exact hst hw
  obtain ⟨k, hk⟩ := htree w (by omega) hwr
  have hiter : ∀ j, (st tl hd O r t).2 ((pO hd O r)^[j] w) < dg tl ((pO hd O r)^[j] w) := by
    intro j
    induction j with
    | zero => simpa using hw
    | succ j ih => rw [Function.iterate_succ_apply']; exact hclosed _ ih
  have := hiter k
  rw [hk] at this
  exact hst this

include e in
lemma NS_all (hbal : ∀ w, (univ.filter (fun a => hd a = w)).card = dg tl w)
    (htree : GT tl r (pO hd O r)) : ∀ t ≤ Fintype.card A, NS tl hd O r t := by
  intro t
  induction t with
  | zero => intro _ s hs; omega
  | succ t ih =>
    intro ht s hs
    have hNS := ih (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact hNS s hs
    · exact not_stuck O r e hbal htree (by omega) hNS

end

lemma rk_inj {tl : A → V} (O : Ords tl) {a b : A} (ht : tl a = tl b) (hr : rk O a = rk O b) :
    a = b := by
  rw [rk_eq O (v := tl b) ht, rk_eq O (v := tl b) rfl] at hr
  have := (O (tl b)).symm.injective (Fin.ext hr)
  exact congrArg Subtype.val this

lemma ords_ext {tl : A → V} {O O' : Ords tl} (h : ∀ a, rk O a = rk O' a) : O = O' := by
  funext v
  apply Equiv.symm_bijective.injective
  ext ⟨a, ha⟩
  have := h a
  rw [rk_eq O ha, rk_eq O' ha] at this
  exact this

/-- a closed Euler tour, listing every arc once -/
def IsTourG (tl hd : A → V) {L : ℕ} (hL : 0 < L) (σ : Fin L ≃ A) : Prop :=
  ∀ t : Fin L, hd (σ t) = tl (σ ⟨(t.val + 1) % L, Nat.mod_lt _ hL⟩)

section Walk2
variable {tl hd : A → V} (O : Ords tl) (r : V) (e : A)
  (hbal : ∀ w, (univ.filter (fun a => hd a = w)).card = dg tl w)
  (htree : GT tl r (pO hd O r))

include hbal htree e

lemma NS_of_lt {t : ℕ} (ht : t < Fintype.card A) : NS tl hd O r (t + 1) :=
  NS_all O r e hbal htree (t + 1) (by omega)

lemma arcAt_bij : Function.Bijective
    (fun i : Fin (Fintype.card A) => arcAt tl hd O r e i.val) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j h => Fin.ext ?_, by simp⟩
  exact arcAt_inj O r e (NS_all O r e hbal htree _ le_rfl) i.2 j.2 h

lemma cnt_full (P : A → Prop) [DecidablePred P] :
    (∑ s ∈ range (Fintype.card A), if P (arcAt tl hd O r e s) then 1 else 0) =
      (univ.filter P).card := by
  rw [Finset.sum_range (fun s => if P (arcAt tl hd O r e s) then 1 else 0)]
  rw [Function.Bijective.sum_comp (arcAt_bij O r e hbal htree)
    (fun a => if P a then 1 else 0)]
  simp

lemma link {t : ℕ} (ht : t + 1 < Fintype.card A) :
    hd (arcAt tl hd O r e t) = tl (arcAt tl hd O r e (t + 1)) := by
  have h1 := NS_of_lt O r e hbal htree ht
  rw [tl_arcAt O r e (h1 (t + 1) (by omega)), st_succ O r e (h1 t (by omega))]

lemma wrap (hpos : 0 < Fintype.card A) :
    hd (arcAt tl hd O r e (Fintype.card A - 1)) = r := by
  have hN := NS_all O r e hbal htree _ le_rfl
  have hsucc := st_succ O r e (hN (Fintype.card A - 1) (by omega))
  rw [Nat.sub_add_cancel hpos] at hsucc
  obtain ⟨_, hflow⟩ := inv O r e _ hN
  have h := hflow r
  rw [if_pos rfl, hsucc] at h
  simp only at h
  have h1 : inCnt tl hd O r e (Fintype.card A) r = dg tl r := by
    rw [inCnt, cnt_full O r e hbal htree (fun a => hd a = r), hbal]
  have h2 : outCnt tl hd O r e (Fintype.card A) r = dg tl r := by
    rw [outCnt, cnt_full O r e hbal htree (fun a => tl a = r), dg, Fintype.card_subtype]
  rw [h1, h2] at h
  by_contra hne
  rw [if_neg (Ne.symm hne)] at h
  omega

lemma arcAt_zero (hpos : 0 < Fintype.card A) (her : tl e = r) (he : rk O e = 0) :
    arcAt tl hd O r e 0 = e := by
  have h0 := NS_of_lt O r e hbal htree hpos 0 (by omega)
  apply rk_inj O
  · rw [tl_arcAt O r e h0, her]; rfl
  · rw [rk_arcAt O r e h0, he]; rfl

/-- the Euler tour traced by the walk -/
noncomputable def walkTour : Fin (Fintype.card A) ≃ A :=
  Equiv.ofBijective _ (arcAt_bij O r e hbal htree)

lemma walkTour_apply (i : Fin (Fintype.card A)) :
    walkTour O r e hbal htree i = arcAt tl hd O r e i.val := rfl

lemma walkTour_isTour (hpos : 0 < Fintype.card A) (her : tl e = r) (he : rk O e = 0) :
    IsTourG tl hd hpos (walkTour O r e hbal htree) := by
  intro t
  simp only [walkTour_apply]
  by_cases ht : t.val + 1 < Fintype.card A
  · rw [Nat.mod_eq_of_lt ht]; exact link O r e hbal htree ht
  · have : t.val = Fintype.card A - 1 := by omega
    rw [this, Nat.sub_add_cancel hpos, Nat.mod_self, arcAt_zero O r e hbal htree hpos her he,
      her]
    exact wrap O r e hbal htree hpos

lemma walkTour_zero (hpos : 0 < Fintype.card A) (her : tl e = r) (he : rk O e = 0) :
    walkTour O r e hbal htree ⟨0, hpos⟩ = e :=
  arcAt_zero O r e hbal htree hpos her he

end Walk2

section Phi
variable {tl hd : A → V} (hN : 0 < Fintype.card A) (σ : Fin (Fintype.card A) ≃ A)

/-- the tour as a periodic sequence -/
def gσ (hN : 0 < Fintype.card A) (σ : Fin (Fintype.card A) ≃ A) (t : ℕ) : A :=
  σ ⟨t % Fintype.card A, Nat.mod_lt _ hN⟩

lemma gσ_lt {t : ℕ} (ht : t < Fintype.card A) : gσ hN σ t = σ ⟨t, ht⟩ := by
  simp [gσ, Nat.mod_eq_of_lt ht]

lemma gσ_symm (a : A) : gσ hN σ (σ.symm a).val = a := by
  rw [gσ_lt hN σ (σ.symm a).2]; simp

/-- number of earlier exits from the tail of `a` -/
def rkσ (tl : A → V) (hN : 0 < Fintype.card A) (σ : Fin (Fintype.card A) ≃ A) (a : A) : ℕ :=
  ∑ s ∈ range (σ.symm a).val, if tl (gσ hN σ s) = tl a then 1 else 0

lemma rkσ_lt (a : A) : rkσ tl hN σ a < dg tl (tl a) := by
  have hle : rkσ tl hN σ a ≤ ((univ.filter (fun b => tl b = tl a)).erase a).card := by
    unfold rkσ; rw [sum_boole]; simp only [Nat.cast_id]
    apply card_le_card_of_injOn (gσ hN σ)
    · intro s hs
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs
      have hsN : s < Fintype.card A := lt_trans hs.1 (σ.symm a).2
      rw [mem_coe, mem_erase, mem_filter]
      refine ⟨?_, mem_univ _, hs.2⟩
      intro h
      rw [gσ_lt hN σ hsN] at h
      have h2 : σ.symm a = ⟨s, hsN⟩ := by rw [← h]; simp
      rw [h2] at hs
      exact lt_irrefl _ hs.1
    · intro s₁ hs₁ s₂ hs₂ heq
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hs₁ hs₂
      have h1 : s₁ < Fintype.card A := lt_trans hs₁.1 (σ.symm a).2
      have h2 : s₂ < Fintype.card A := lt_trans hs₂.1 (σ.symm a).2
      rw [gσ_lt hN σ h1, gσ_lt hN σ h2] at heq
      exact congrArg Fin.val (σ.injective heq)
  have hmem : a ∈ univ.filter (fun b => tl b = tl a) := by simp
  rw [card_erase_of_mem hmem] at hle
  have : (univ.filter (fun b => tl b = tl a)).card = dg tl (tl a) := by
    rw [dg, Fintype.card_subtype]
  have hpos := card_pos.mpr ⟨a, hmem⟩
  omega

lemma rkσ_mono {a b : A} (hab : tl a = tl b) (h : (σ.symm a).val < (σ.symm b).val) :
    rkσ tl hN σ a < rkσ tl hN σ b := by
  have h1 : rkσ tl hN σ a + 1 =
      ∑ s ∈ range ((σ.symm a).val + 1), if tl (gσ hN σ s) = tl b then 1 else 0 := by
    rw [sum_range_succ, gσ_symm, if_pos hab, rkσ, hab]
  have h2 : (∑ s ∈ range ((σ.symm a).val + 1), if tl (gσ hN σ s) = tl b then 1 else 0) ≤
      rkσ tl hN σ b :=
    sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr h) (fun _ _ _ => Nat.zero_le _)
  omega

lemma rkσ_inj {a b : A} (hab : tl a = tl b) (h : rkσ tl hN σ a = rkσ tl hN σ b) : a = b := by
  rcases lt_trichotomy (σ.symm a).val (σ.symm b).val with h1 | h1 | h1
  · exact absurd h (ne_of_lt (rkσ_mono hN σ hab h1))
  · exact σ.symm.injective (Fin.ext h1)
  · exact absurd h.symm (ne_of_lt (rkσ_mono hN σ hab.symm h1))

/-- the out-arc orderings read off from a tour -/
noncomputable def Phi (tl : A → V) (hN : 0 < Fintype.card A) (σ : Fin (Fintype.card A) ≃ A) :
    Ords tl := fun v =>
  (Equiv.ofBijective (fun a : Out tl v => (⟨rkσ tl hN σ a.1,
      by have := rkσ_lt (tl := tl) hN σ a.1; rwa [a.2] at this⟩ : Fin (dg tl v)))
    (by
      rw [Fintype.bijective_iff_injective_and_card]
      refine ⟨fun a b h => Subtype.ext ?_, (Fintype.card_fin _).symm⟩
      exact rkσ_inj (tl := tl) hN σ (a.2.trans b.2.symm) (congrArg Fin.val h))).symm

lemma rk_Phi (a : A) : rk (Phi tl hN σ) a = rkσ tl hN σ a := by
  unfold rk Phi; simp

lemma g_link (htour : IsTourG tl hd hN σ) (t : ℕ) : hd (gσ hN σ t) = tl (gσ hN σ (t + 1)) := by
  have := htour ⟨t % Fintype.card A, Nat.mod_lt _ hN⟩
  have key : (t % Fintype.card A + 1) % Fintype.card A = (t + 1) % Fintype.card A := by
    rw [Nat.add_mod (t % Fintype.card A) 1, Nat.mod_mod, ← Nat.add_mod]
  unfold gσ
  rw [this]
  exact congrArg (fun i => tl (σ i)) (Fin.ext key)

variable (r : V) (e : A)

include e in
lemma walk_Phi (htour : IsTourG tl hd hN σ) (hr : tl (σ ⟨0, hN⟩) = r) :
    ∀ t < Fintype.card A, st tl hd (Phi tl hN σ) r t =
      (tl (gσ hN σ t), fun w => ∑ s ∈ range t, if tl (gσ hN σ s) = w then 1 else 0) := by
  have hstep : ∀ t < Fintype.card A, st tl hd (Phi tl hN σ) r t =
      (tl (gσ hN σ t), fun w => ∑ s ∈ range t, if tl (gσ hN σ s) = w then 1 else 0) →
      (st tl hd (Phi tl hN σ) r t).2 (st tl hd (Phi tl hN σ) r t).1 <
        dg tl (st tl hd (Phi tl hN σ) r t).1 ∧ arcAt tl hd (Phi tl hN σ) r e t = gσ hN σ t := by
    intro t ht hst
    have hsym : (σ.symm (gσ hN σ t)).val = t := by rw [gσ_lt hN σ ht]; simp
    have hc : (st tl hd (Phi tl hN σ) r t).2 (st tl hd (Phi tl hN σ) r t).1 =
        rkσ tl hN σ (gσ hN σ t) := by
      rw [hst, rkσ, hsym]
    have hns : (st tl hd (Phi tl hN σ) r t).2 (st tl hd (Phi tl hN σ) r t).1 <
        dg tl (st tl hd (Phi tl hN σ) r t).1 := by
      rw [hc]; rw [hst]; exact rkσ_lt hN σ _
    refine ⟨hns, ?_⟩
    apply rk_inj (Phi tl hN σ)
    · rw [tl_arcAt _ r e hns, hst]
    · rw [rk_arcAt _ r e hns, hc, rk_Phi]
  intro t
  induction t with
  | zero =>
    intro _
    simp only [st, range_zero, sum_empty]
    rw [gσ_lt hN σ hN]
    simp [hr]
    rfl
  | succ t ih =>
    intro ht
    have hst := ih (by omega)
    obtain ⟨hns, harc⟩ := hstep t (by omega) hst
    rw [st_succ _ r e hns, harc, g_link hN σ htour t]
    congr 1
    funext w
    rw [hst, sum_range_succ]
    simp only
    by_cases hw : w = tl (gσ hN σ t)
    · subst hw; simp
    · rw [Function.update_of_ne hw]; simp [Ne.symm hw]

lemma arcAt_Phi (htour : IsTourG tl hd hN σ) (hr : tl (σ ⟨0, hN⟩) = r) {t : ℕ}
    (ht : t < Fintype.card A) : arcAt tl hd (Phi tl hN σ) r e t = gσ hN σ t := by
  have hst := walk_Phi hN σ r e htour hr t ht
  have hsym : (σ.symm (gσ hN σ t)).val = t := by rw [gσ_lt hN σ ht]; simp
  have hc : (st tl hd (Phi tl hN σ) r t).2 (st tl hd (Phi tl hN σ) r t).1 =
      rkσ tl hN σ (gσ hN σ t) := by
    rw [hst, rkσ, hsym]
  have hns : (st tl hd (Phi tl hN σ) r t).2 (st tl hd (Phi tl hN σ) r t).1 <
      dg tl (st tl hd (Phi tl hN σ) r t).1 := by
    rw [hc]; rw [hst]; exact rkσ_lt hN σ _
  apply rk_inj (Phi tl hN σ)
  · rw [tl_arcAt _ r e hns, hst]
  · rw [rk_arcAt _ r e hns, hc, rk_Phi]

lemma GT_Phi (htour : IsTourG tl hd hN σ) (hr : tl (σ ⟨0, hN⟩) = r) :
    GT tl r (pO hd (Phi tl hN σ) r) := by
  -- the last exit from `w`
  have hlast : ∀ w (h : 0 < dg tl w), ∀ b, tl b = w →
      (σ.symm b).val ≤ (σ.symm ((Phi tl hN σ) w ⟨dg tl w - 1, by omega⟩).1).val := by
    intro w h b hb
    by_contra hlt
    push Not at hlt
    have h1 := rkσ_mono hN σ ((((Phi tl hN σ) w _).2).trans hb.symm) hlt
    have h2 := rkσ_lt (tl := tl) hN σ b
    have h3 : rk (Phi tl hN σ) ((Phi tl hN σ) w ⟨dg tl w - 1, by omega⟩).1 = dg tl w - 1 :=
      rk_O (Phi tl hN σ) w _
    rw [rk_Phi] at h3
    rw [h3] at h1
    rw [hb] at h2
    omega
  have hp : ∀ w (h : 0 < dg tl w ∧ w ≠ r),
      pO hd (Phi tl hN σ) r w = hd ((Phi tl hN σ) w ⟨dg tl w - 1, by omega⟩).1 := by
    intro w h; unfold pO; rw [dif_pos h]
  have key : ∀ w (h : 0 < dg tl w ∧ w ≠ r), pO hd (Phi tl hN σ) r w ≠ r →
      ∃ h' : 0 < dg tl (pO hd (Phi tl hN σ) r w) ∧ pO hd (Phi tl hN σ) r w ≠ r,
        (σ.symm ((Phi tl hN σ) w ⟨dg tl w - 1, by omega⟩).1).val <
          (σ.symm ((Phi tl hN σ) (pO hd (Phi tl hN σ) r w) ⟨dg tl (pO hd (Phi tl hN σ) r w) - 1, by omega⟩).1).val := by
    intro w h hpr
    set ℓ := ((Phi tl hN σ) w ⟨dg tl w - 1, by omega⟩).1 with hℓ
    set i := σ.symm ℓ with hi
    have hσi : σ i = ℓ := by simp [hi]
    have ht := htour i
    rw [hσi] at ht
    have hiN : i.val + 1 < Fintype.card A := by
      by_contra hge
      have : (i.val + 1) % Fintype.card A = 0 := by
        have : i.val + 1 = Fintype.card A := by have := i.2; omega
        rw [this, Nat.mod_self]
      have h0 : (⟨(i.val + 1) % Fintype.card A, Nat.mod_lt _ hN⟩ : Fin (Fintype.card A)) = ⟨0, hN⟩ := Fin.ext this
      rw [h0, hr] at ht
      exact hpr (by rw [hp w h, ← hℓ, ht])
    set b := σ ⟨i.val + 1, hiN⟩ with hb
    have hbt : tl b = pO hd (Phi tl hN σ) r w := by
      rw [hp w h, ← hℓ, ht, hb]
      congr 2
      exact Fin.ext (Nat.mod_eq_of_lt hiN).symm
    have hdpos : 0 < dg tl (pO hd (Phi tl hN σ) r w) := by
      rw [dg]; exact Fintype.card_pos_iff.mpr ⟨⟨b, hbt⟩⟩
    refine ⟨⟨hdpos, hpr⟩, ?_⟩
    have := hlast _ hdpos b hbt
    have hbs : (σ.symm b).val = i.val + 1 := by simp [hb]
    rw [hbs] at this
    omega
  -- strong induction on the remaining time
  have main : ∀ k, ∀ w (h : 0 < dg tl w ∧ w ≠ r),
      Fintype.card A - (σ.symm ((Phi tl hN σ) w ⟨dg tl w - 1, by omega⟩).1).val ≤ k →
      ∃ j, (pO hd (Phi tl hN σ) r)^[j] w = r := by
    intro k
    induction k with
    | zero =>
      intro w h hk
      have := (σ.symm ((Phi tl hN σ) w ⟨dg tl w - 1, by omega⟩).1).2
      omega
    | succ k ih =>
      intro w h hk
      by_cases hpr : pO hd (Phi tl hN σ) r w = r
      · exact ⟨1, by simpa using hpr⟩
      · obtain ⟨h', hlt⟩ := key w h hpr
        obtain ⟨j, hj⟩ := ih _ h' (by omega)
        exact ⟨j + 1, by rw [Function.iterate_succ_apply]; exact hj⟩
  intro w hw hwr
  exact main _ w ⟨hw, hwr⟩ le_rfl

lemma rk_Phi_e (he : σ ⟨0, hN⟩ = e) : rk (Phi tl hN σ) e = 0 := by
  rw [rk_Phi, rkσ]
  have : (σ.symm e).val = 0 := by rw [← he]; simp
  rw [this]; simp

end Phi

section Bij
variable {tl hd : A → V} (r : V) (e : A)
  (hbal : ∀ w, (univ.filter (fun a => hd a = w)).card = dg tl w)

lemma Phi_walk (O : Ords tl) (htree : GT tl r (pO hd O r)) (hpos : 0 < Fintype.card A) :
    Phi tl hpos (walkTour O r e hbal htree) = O := by
  apply ords_ext
  intro a
  rw [rk_Phi, rkσ]
  set σ := walkTour O r e hbal htree
  set t := (σ.symm a).val with ht
  have hNS : NS tl hd O r (t + 1) := NS_of_lt O r e hbal htree (σ.symm a).2
  have hat : arcAt tl hd O r e t = a := by
    rw [ht, ← walkTour_apply O r e hbal htree]; simp [σ]
  have : (∑ s ∈ range t, if tl (gσ hpos σ s) = tl a then 1 else 0) =
      outCnt tl hd O r e t (tl a) := by
    unfold outCnt
    refine sum_congr rfl fun s hs => ?_
    have hsN : s < Fintype.card A := lt_trans (mem_range.mp hs) (σ.symm a).2
    rw [gσ_lt hpos σ hsN, walkTour_apply]
  rw [this, ← hat, rk_arcAt' O r e hNS]

include hbal in
open Classical in
theorem card_tours (hN : 0 < Fintype.card A) (her : tl e = r) :
    Fintype.card {σ : Fin (Fintype.card A) ≃ A // IsTourG tl hd hN σ ∧ σ ⟨0, hN⟩ = e} =
      Fintype.card {O : Ords tl // rk O e = 0 ∧ GT tl r (pO hd O r)} := by
  apply Fintype.card_congr
  exact {
    toFun := fun σ => ⟨Phi tl hN σ.1, rk_Phi_e hN σ.1 e σ.2.2,
      GT_Phi hN σ.1 r σ.2.1 (by rw [σ.2.2, her])⟩
    invFun := fun O => ⟨walkTour O.1 r e hbal O.2.2,
      walkTour_isTour O.1 r e hbal O.2.2 hN her O.2.1,
      walkTour_zero O.1 r e hbal O.2.2 hN her O.2.1⟩
    left_inv := fun σ => by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      simp only
      rw [walkTour_apply, arcAt_Phi hN σ.1 r e σ.2.1 (by rw [σ.2.2, her]) i.2, gσ_lt hN _ i.2]
    right_inv := fun O => by
      apply Subtype.ext
      exact Phi_walk r e hbal O.1 O.2.2 hN }

end Bij

section Fix
variable {X : Type*} [Fintype X] [DecidableEq X]

lemma card_fix {d : ℕ} (hd : Fintype.card X = d) (i : Fin d) (x : X) :
    Fintype.card {g : Fin d ≃ X // g i = x} = (d - 1).factorial := by
  subst hd
  have hsame : ∀ y, Fintype.card {g : Fin (Fintype.card X) ≃ X // g i = y} =
      Fintype.card {g : Fin (Fintype.card X) ≃ X // g i = x} := by
    intro y
    apply Fintype.card_congr
    exact {
      toFun := fun g => ⟨g.1.trans (Equiv.swap y x), by simp [g.2]⟩
      invFun := fun g => ⟨g.1.trans (Equiv.swap y x), by simp [g.2]⟩
      left_inv := fun g => by ext; simp
      right_inv := fun g => by ext; simp }
  have htot : ∑ y : X, Fintype.card {g : Fin (Fintype.card X) ≃ X // g i = y} =
      (Fintype.card X).factorial := by
    rw [← Fintype.card_sigma]
    refine (Fintype.card_congr (Equiv.sigmaFiberEquiv (fun g : Fin _ ≃ X => g i))).trans ?_
    rw [Fintype.card_equiv (Fintype.equivFin X).symm, Fintype.card_fin]
  simp only [hsame, sum_const, card_univ, smul_eq_mul] at htot
  have hpos : 0 < Fintype.card X := by have := i.2; omega
  rw [← Nat.mul_factorial_pred hpos.ne'] at htot
  exact Nat.eq_of_mul_eq_mul_left hpos htot

lemma sum_fix {d : ℕ} (hd : Fintype.card X = d) (i : Fin d) (P : X → Prop) [DecidablePred P] :
    (∑ g : Fin d ≃ X, if P (g i) then 1 else 0) =
      (univ.filter P).card * (d - 1).factorial := by
  rw [sum_boole, Nat.cast_id,
    card_eq_sum_card_fiberwise (f := fun g => g i) (t := univ.filter P)
      (fun g hg => by simpa using hg)]
  rw [card_eq_sum_ones (univ.filter P), sum_mul, one_mul]
  refine sum_congr rfl fun y hy => ?_
  rw [← card_fix hd i y, Fintype.card_subtype]
  congr 1
  ext g
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  intro h; rw [h]; simpa using hy

lemma card_equiv_empty {d : ℕ} (hd : Fintype.card X = d) (h0 : d = 0) :
    Fintype.card (Fin d ≃ X) = 1 := by
  subst hd
  rw [Fintype.card_equiv (Fintype.equivFin X).symm, Fintype.card_fin, h0]; rfl

end Fix

section Good

/-- the per-vertex constraint on an ordering -/
def Q (tl hd : A → V) (r : V) (e : A) (p : V → V) (v : V) (g : Fin (dg tl v) ≃ Out tl v) :
    Prop :=
  (∀ h : tl e = v, (g.symm ⟨e, h⟩).val = 0) ∧
  (∀ h : 0 < dg tl v, v ≠ r → hd (g ⟨dg tl v - 1, by omega⟩).1 = p v)

variable {tl hd : A → V} (r : V) (e : A)

lemma Q_iff (p : V → V) (hfix : ∀ v, ¬(0 < dg tl v ∧ v ≠ r) → p v = v) (O : Ords tl) :
    (∀ v, Q tl hd r e p v (O v)) ↔ (pO hd O r = p ∧ rk O e = 0) := by
  constructor
  · intro h
    refine ⟨funext fun v => ?_, ?_⟩
    · unfold pO
      split_ifs with hv
      · exact (h v).2 hv.1 hv.2
      · exact (hfix v hv).symm
    · rw [rk_eq O rfl]
      exact (h (tl e)).1 rfl
  · rintro ⟨hp, hr⟩ v
    refine ⟨fun h => ?_, fun h hv => ?_⟩
    · rw [← rk_eq O h]; exact hr
    · rw [← hp]; unfold pO; rw [dif_pos ⟨h, hv⟩]

open Classical in
lemma sum_Q (her : tl e = r) (p : V → V) (v : V) :
    (∑ g : Fin (dg tl v) ≃ Out tl v, if Q tl hd r e p v g then 1 else 0) =
      (if 0 < dg tl v ∧ v ≠ r then (univ.filter (fun a => tl a = v ∧ hd a = p v)).card
        else 1) * (dg tl v - 1).factorial := by
  by_cases hvr : v = r
  · subst hvr
    rw [if_neg (by tauto), one_mul]
    have hpos : 0 < dg tl v := Fintype.card_pos_iff.mpr ⟨⟨e, her⟩⟩
    have := sum_fix (X := Out tl v) (d := dg tl v) rfl ⟨0, hpos⟩ (fun x => x = ⟨e, her⟩)
    have h1 : (univ.filter (fun x : Out tl v => x = ⟨e, her⟩)).card = 1 := by
      rw [filter_eq']; simp
    rw [h1, one_mul] at this
    rw [← this]
    refine sum_congr rfl fun g _ => if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, _⟩
      have h2 : g.symm ⟨e, her⟩ = ⟨0, hpos⟩ := Fin.ext (h1 her)
      exact (Equiv.symm_apply_eq g).mp h2 |>.symm
    · intro h
      refine ⟨fun h' => ?_, fun _ hne => absurd rfl hne⟩
      have : g.symm ⟨e, h'⟩ = ⟨0, hpos⟩ := by rw [Equiv.symm_apply_eq, h]
      rw [this]
  · by_cases hd0 : 0 < dg tl v
    · rw [if_pos ⟨hd0, hvr⟩]
      have := sum_fix (X := Out tl v) (d := dg tl v) rfl ⟨dg tl v - 1, by omega⟩
        (fun x => hd x.1 = p v)
      have hcard : (univ.filter (fun x : Out tl v => hd x.1 = p v)).card =
          (univ.filter (fun a => tl a = v ∧ hd a = p v)).card := by
        apply card_bij (fun x _ => x.1)
        · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact ⟨x.2, hx⟩
        · intro x _ y _ h; exact Subtype.ext h
        · intro a ha
          simp only [mem_filter, mem_univ, true_and] at ha
          exact ⟨⟨a, ha.1⟩, by simp [ha.2], rfl⟩
      rw [← hcard, ← this]
      refine sum_congr rfl fun g _ => if_congr ?_ rfl rfl
      constructor
      · rintro ⟨_, h2⟩; exact h2 hd0 hvr
      · intro h
        exact ⟨fun h' => absurd (her.symm.trans h') (Ne.symm hvr), fun _ _ => h⟩
    · rw [if_neg (by tauto), one_mul]
      have h0 : dg tl v = 0 := by omega
      rw [show (dg tl v - 1).factorial = 1 by rw [h0]; rfl]
      have hQ : ∀ g, Q tl hd r e p v g := fun g =>
        ⟨fun h' => absurd (her.symm.trans h') (Ne.symm hvr), fun h _ => absurd h hd0⟩
      simp only [hQ, if_true, sum_const, card_univ, smul_eq_mul, mul_one]
      exact card_equiv_empty rfl h0

open Classical in
theorem card_good (her : tl e = r) :
    Fintype.card {O : Ords tl // rk O e = 0 ∧ GT tl r (pO hd O r)} =
      (∑ p : V → V, if (∀ v, ¬(0 < dg tl v ∧ v ≠ r) → p v = v) ∧ GT tl r p then
        ∏ v ∈ univ.filter (fun v => 0 < dg tl v ∧ v ≠ r),
          (univ.filter (fun a => tl a = v ∧ hd a = p v)).card else 0) *
      ∏ v, (dg tl v - 1).factorial := by
  rw [Fintype.card_subtype, card_filter]
  have h1 : ∀ O : Ords tl, (if rk O e = 0 ∧ GT tl r (pO hd O r) then 1 else 0) =
      ∑ p : V → V, if pO hd O r = p then (if rk O e = 0 ∧ GT tl r p then 1 else 0) else 0 := by
    intro O; rw [sum_ite_eq]; simp
  rw [sum_congr rfl (fun O _ => h1 O), sum_comm, sum_mul]
  refine sum_congr rfl fun p _ => ?_
  by_cases hg : GT tl r p
  · by_cases hf : ∀ v, ¬(0 < dg tl v ∧ v ≠ r) → p v = v
    · rw [if_pos ⟨hf, hg⟩]
      have h2 : ∀ O : Ords tl,
          (if pO hd O r = p then (if rk O e = 0 ∧ GT tl r p then 1 else 0) else 0) =
            ∏ v, if Q tl hd r e p v (O v) then 1 else 0 := by
        intro O
        rw [prod_boole]
        have := Q_iff (hd := hd) r e p hf O
        by_cases hq : ∀ v, Q tl hd r e p v (O v)
        · obtain ⟨hp, hr⟩ := this.mp hq
          rw [if_pos (fun v _ => hq v), if_pos hp, if_pos ⟨hr, hg⟩]
        · have hq' : ¬ ∀ i ∈ univ, Q tl hd r e p i (O i) := fun h => hq fun v => h v (mem_univ v)
          rw [if_neg hq']
          split_ifs with hp hr
          · exact absurd (this.mpr ⟨hp, hr.1⟩) hq
          · rfl
          · rfl
      rw [sum_congr rfl (fun O _ => h2 O),
        ← Fintype.prod_sum (fun v (g : Fin (dg tl v) ≃ Out tl v) =>
          if Q tl hd r e p v g then 1 else 0)]
      rw [prod_congr rfl (fun v _ => sum_Q r e her p v), prod_mul_distrib, prod_filter]
    · rw [if_neg (fun h => hf h.1), zero_mul]
      apply sum_eq_zero; intro O _
      rw [if_neg]; rintro rfl; apply hf; intro v hv; unfold pO; rw [dif_neg hv]
  · rw [if_neg (fun h => hg h.2), zero_mul]
    apply sum_eq_zero; intro O _
    split_ifs with h1 h2
    · exact absurd h2.2 hg
    · rfl
    · rfl

end Good

section Rot
variable {tl hd : A → V}

lemma tour_iff [NeZero (Fintype.card A)] (hN : 0 < Fintype.card A)
    (σ : Fin (Fintype.card A) ≃ A) :
    IsTourG tl hd hN σ ↔ ∀ t, hd (σ t) = tl (σ (t + 1)) := by
  have key : ∀ t : Fin (Fintype.card A),
      (⟨(t.val + 1) % Fintype.card A, Nat.mod_lt _ hN⟩ : Fin (Fintype.card A)) = t + 1 := by
    intro t
    apply Fin.ext
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  unfold IsTourG
  simp only [key]

open Classical in
theorem card_rot (hN : 0 < Fintype.card A) (e : A) :
    Fintype.card {σ : Fin (Fintype.card A) ≃ A // IsTourG tl hd hN σ} =
      Fintype.card A *
        Fintype.card {σ : Fin (Fintype.card A) ≃ A // IsTourG tl hd hN σ ∧ σ ⟨0, hN⟩ = e} := by
  have : NeZero (Fintype.card A) := ⟨hN.ne'⟩
  have h0 : (⟨0, hN⟩ : Fin (Fintype.card A)) = 0 := rfl
  have hrot : ∀ (k : Fin (Fintype.card A)) (σ : Fin (Fintype.card A) ≃ A),
      IsTourG tl hd hN σ → IsTourG tl hd hN ((Equiv.addRight k).trans σ) := by
    intro k σ h
    rw [tour_iff] at h ⊢
    intro t
    simp only [Equiv.trans_apply, Equiv.coe_addRight]
    rw [h (t + k), add_right_comm]
  rw [show Fintype.card A *
        Fintype.card {σ : Fin (Fintype.card A) ≃ A // IsTourG tl hd hN σ ∧ σ ⟨0, hN⟩ = e} =
      Fintype.card (Fin (Fintype.card A) ×
        {σ : Fin (Fintype.card A) ≃ A // IsTourG tl hd hN σ ∧ σ ⟨0, hN⟩ = e}) by
    rw [Fintype.card_prod, Fintype.card_fin]]
  apply Fintype.card_congr
  exact {
    toFun := fun σ => (σ.1.symm e, ⟨(Equiv.addRight (σ.1.symm e)).trans σ.1,
      hrot _ _ σ.2, by simp [h0]⟩)
    invFun := fun x => ⟨(Equiv.addRight (-x.1)).trans x.2.1, hrot _ _ x.2.2.1⟩
    left_inv := fun σ => by
      apply Subtype.ext; apply Equiv.ext; intro t; simp
    right_inv := fun x => by
      obtain ⟨k, τ, hτ, hτe⟩ := x
      have hk : ((Equiv.addRight (-k)).trans τ).symm e = k := by
        rw [Equiv.symm_apply_eq]; simp [← hτe, h0]
      simp only [hk]
      refine Prod.ext rfl (Subtype.ext (Equiv.ext fun t => ?_))
      simp }

end Rot

end BESTAux

open BESTAux Classical in
theorem solution {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
    (tl hd : A → V) (hN : 0 < Fintype.card A)
    (hbal : ∀ v, (univ.filter (fun a => hd a = v)).card = (univ.filter (fun a => tl a = v)).card)
    (r : V) (hr : ∃ a, tl a = r) :
    Fintype.card {σ : Fin (Fintype.card A) ≃ A // ∀ t : Fin (Fintype.card A),
        hd (σ t) = tl (σ ⟨(t.val + 1) % Fintype.card A, Nat.mod_lt _ hN⟩)} =
      Fintype.card A *
        (∑ p : V → V,
          if (∀ v, ¬(0 < (univ.filter (fun a => tl a = v)).card ∧ v ≠ r) → p v = v) ∧
              (∀ v, 0 < (univ.filter (fun a => tl a = v)).card → v ≠ r → ∃ k, p^[k] v = r) then
            ∏ v ∈ univ.filter (fun v => 0 < (univ.filter (fun a => tl a = v)).card ∧ v ≠ r),
              (univ.filter (fun a => tl a = v ∧ hd a = p v)).card
          else 0) *
        ∏ v, ((univ.filter (fun a => tl a = v)).card - 1).factorial := by
  obtain ⟨e, her⟩ := hr
  have hdg : ∀ v, dg tl v = (univ.filter (fun a => tl a = v)).card := fun v => by
    rw [dg, Fintype.card_subtype]
  have hbal' : ∀ w, (univ.filter (fun a => hd a = w)).card = dg tl w := fun w => by
    rw [hbal, hdg]
  have h1 : Fintype.card {σ : Fin (Fintype.card A) ≃ A // ∀ t : Fin (Fintype.card A),
        hd (σ t) = tl (σ ⟨(t.val + 1) % Fintype.card A, Nat.mod_lt _ hN⟩)} =
      Fintype.card {σ // IsTourG tl hd hN σ} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun σ => Iff.rfl))
  rw [h1, card_rot hN e, card_tours r e hbal' hN her, card_good r e her]
  simp only [hdg, GT]
  rw [mul_assoc]
