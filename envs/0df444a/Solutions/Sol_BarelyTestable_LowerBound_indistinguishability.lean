-- Prove2me | solution 1 for BarelyTestable.LowerBound.indistinguishability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:32:58.73973+00:00
-- url     : https://prove2.me/submissions/f7a71734-1306-4712-995a-9af9ebf75596

import Mathlib
import Definitions.Def_BarelyTestable_LowerBound_Discovery
import Theorems.Thm_BarelyTestable_LowerBound_center_discovery

set_option autoImplicit false

open BarelyTestable.LowerBound NonmonotoneSubmod.Shared MeasureTheory

namespace BTHelper_indist

section Run
variable {ι : Type} (A : Procedure ι)

lemma run_prefix (f : Oracle ι) : ∀ (k : ℕ) (h : History ι), ∃ rest, (run A f k h).1 = h ++ rest
  | 0, h => by
    rcases hA : A h with b | x <;> simp [run, hA]
  | k + 1, h => by
    rcases hA : A h with b | x
    · simp [run, hA]
    · obtain ⟨rest, hr⟩ := run_prefix f k (h ++ [(x, f x)])
      refine ⟨(x, f x) :: rest, ?_⟩
      simp [run, hA, hr]

lemma run_length_le (f : Oracle ι) : ∀ (k : ℕ) (h : History ι),
    (run A f k h).1.length ≤ h.length + k
  | 0, h => by
    rcases hA : A h with b | x <;> simp [run, hA]
  | k + 1, h => by
    rcases hA : A h with b | x
    · simp [run, hA]
    · have := run_length_le f k (h ++ [(x, f x)])
      simp only [run, hA]
      simp at this
      omega

lemma run_take (f : Oracle ι) : ∀ (t k : ℕ) (h : History ι), t ≤ k →
    (run A f t h).1 = ((run A f k h).1).take (h.length + t)
  | 0, k, h, _ => by
    obtain ⟨rest, hr⟩ := run_prefix A f k h
    rcases hA : A h with b | x <;> simp [run, hA, hr]
  | t + 1, 0, h, hk => by omega
  | t + 1, k + 1, h, hk => by
    rcases hA : A h with b | x
    · simp [run, hA]
    · have := run_take f t k (h ++ [(x, f x)]) (by omega)
      simp only [run, hA]
      rw [this]
      simp only [List.length_append, List.length_singleton]
      congr 1
      omega

lemma run_next (f : Oracle ι) : ∀ (k : ℕ) (h : History ι) (j : ℕ), h.length ≤ j →
    ∀ hj : j < (run A f k h).1.length,
      A (((run A f k h).1).take j) = Sum.inr (((run A f k h).1)[j]).1
  | 0, h, j, hle, hj => by
    exfalso
    rcases hA : A h with b | x <;> simp [run, hA] at hj <;> omega
  | k + 1, h, j, hle, hj => by
    rcases hA : A h with b | x
    · exfalso
      simp [run, hA] at hj; omega
    · have e : run A f (k + 1) h = run A f k (h ++ [(x, f x)]) := by simp [run, hA]
      have hj' : j < (run A f k (h ++ [(x, f x)])).1.length := by rw [← e]; exact hj
      rcases Nat.lt_or_ge j (h ++ [(x, f x)]).length with hlt | hge
      · have hjeq : j = h.length := by simp at hlt; omega
        obtain ⟨rest, hr⟩ := run_prefix A f k (h ++ [(x, f x)])
        simp only [e]
        subst hjeq
        simp only [hr]
        simp [hA]
      · simp only [e]
        exact run_next f k (h ++ [(x, f x)]) j hge hj'

lemma run_local (f g : Oracle ι) : ∀ (k : ℕ) (h : History ι),
    (∀ p ∈ (run A f k h).1, g p.1 = f p.1) → run A g k h = run A f k h
  | 0, h, _ => by
    rcases hA : A h with b | x <;> simp [run, hA]
  | k + 1, h, hag => by
    rcases hA : A h with b | x
    · simp [run, hA]
    · have e : run A f (k + 1) h = run A f k (h ++ [(x, f x)]) := by simp [run, hA]
      rw [e] at hag
      obtain ⟨rest, hr⟩ := run_prefix A f k (h ++ [(x, f x)])
      have hx : g x = f x := hag (x, f x) (by rw [hr]; simp)
      have := run_local f g k (h ++ [(x, f x)]) hag
      simp only [run, hA, hx]
      exact this

lemma run_stable (f : Oracle ι) (b : Bool) : ∀ (k : ℕ) (h : History ι),
    (run A f k h).2 = some b → run A f (k + 1) h = run A f k h
  | 0, h, hb => by
    rcases hA : A h with c | x <;> simp [run, hA] at hb ⊢
  | k + 1, h, hb => by
    rcases hA : A h with c | x
    · simp [run, hA]
    · have e : run A f (k + 1) h = run A f k (h ++ [(x, f x)]) := by simp [run, hA]
      rw [e] at hb
      have := run_stable f b k (h ++ [(x, f x)]) hb
      rw [show run A f (k + 1 + 1) h = run A f (k + 1) (h ++ [(x, f x)]) by simp [run, hA], e,
        this]

lemma run_stable_le (f : Oracle ι) (b : Bool) (k : ℕ) (h : History ι)
    (hb : (run A f k h).2 = some b) : ∀ k', k ≤ k' → (run A f k' h).2 = some b := by
  intro k' hk
  induction k', hk using Nat.le_induction with
  | base => exact hb
  | succ k' _ ih => rw [run_stable A f b k' h ih]; exact ih

lemma accepts_iff (f : Oracle ι) (q : ℕ) (hq : Budget A q) :
    Accepts A f ↔ (run A f q []).2 = some true := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp (hq f)
    have h1 := run_stable_le A f true k [] hk (max k q) (le_max_left _ _)
    have h2 := run_stable_le A f b q [] hb (max k q) (le_max_right _ _)
    rw [h1] at h2
    cases h2
    exact hb
  · intro h; exact ⟨q, h⟩

end Run


section Construction
variable {m : ℕ}

/-- slice 01: action A absent, action B present. -/
def S01 (x : Cube (Coord m)) : Prop := actionA ∉ x ∧ actionB ∈ x
/-- slice 11: both actions present. -/
def S11 (x : Cube (Coord m)) : Prop := actionA ∈ x ∧ actionB ∈ x

/-- The oracle value at `x` reads the table entry `z`. -/
def Reads (φA φB : LabelMap m) (x : Cube (Coord m)) (z : Address m) : Prop :=
  (S01 x ∧ beta φB (yPart x) = z) ∨ (S11 x ∧ alpha φA (xPart x) = z)

/-- Resampling one table entry. -/
def upd (r : Sample m) (k : Address m) (v : Fin (2 ^ dimension m)) : Sample m :=
  (r.1, r.2.1, Function.update r.2.2 k v)

lemma hard_upd (r : Sample m) (s : Bool) (x : Cube (Coord m)) (k : Address m)
    (v : Fin (2 ^ dimension m)) (hx : ¬ Reads r.1 r.2.1 x k) :
    hard (upd r k v) s x = hard r s x := by
  simp only [Reads, S01, S11, not_or, not_and] at hx
  by_cases hA : actionA ∈ x <;> by_cases hB : actionB ∈ x
  · have := hx.2 ⟨hA, hB⟩
    simp [hard, slice, upd, hA, hB, theta, Function.update_of_ne this]
  · simp [hard, slice, hA, hB]
  · have := hx.1 ⟨hA, hB⟩
    simp [hard, slice, upd, hA, hB, theta, Function.update_of_ne this]
  · simp [hard, slice, hA, hB]

lemma four_le_card : 4 ≤ 2 ^ dimension m := by
  unfold dimension
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (2 * m ^ 2 + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma val_two : ((2 : Fin (2 ^ dimension m)) : ℕ) = 2 := by
  have := four_le_card (m := m)
  show 2 % 2 ^ dimension m = 2
  exact Nat.mod_eq_of_lt (by omega)

/-- No wraparound when shifting by `+2` (YES) or `-2` (NO). -/
def NoWrap (s : Bool) (v : Fin (2 ^ dimension m)) : Prop :=
  if s then v.val + 2 < 2 ^ dimension m else 2 ≤ v.val

def shiftC (s : Bool) : Fin (2 ^ dimension m) := if s then 2 else -2

lemma shiftC_cancel (s : Bool) (v : Fin (2 ^ dimension m)) :
    v + shiftC s + shiftC (!s) = v := by
  cases s <;> simp [shiftC]

lemma noWrap_shift (s : Bool) (v : Fin (2 ^ dimension m)) (h : NoWrap s v) :
    (((v + shiftC s : Fin _) : ℕ) : ℝ) = (v : ℝ) + (if s then 2 else -2) ∧
      NoWrap (!s) (v + shiftC s) := by
  have h2 := val_two (m := m)
  cases s
  · simp only [NoWrap, shiftC] at h ⊢
    simp only [Bool.false_eq_true, if_false, Bool.not_false, if_true]
    have e : ((v + -2 : Fin _) : ℕ) = v - 2 := by
      rw [← sub_eq_add_neg, Fin.coe_sub_iff_le.mpr (by rw [Fin.le_def, h2]; exact h), h2]
    refine ⟨?_, ?_⟩
    · rw [e, Nat.cast_sub h]; push_cast; ring
    · rw [e]; have := v.isLt; omega
  · simp only [NoWrap, shiftC] at h ⊢
    simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false]
    have e : ((v + 2 : Fin _) : ℕ) = v + 2 := by
      rw [Fin.val_add, h2]; exact Nat.mod_eq_of_lt h
    refine ⟨?_, ?_⟩
    · rw [e]; push_cast; ring
    · rw [e]; omega

end Construction

section Coupling
variable {m : ℕ} (A : Procedure (Coord m)) (q : ℕ)

/-- The slice-01 addresses of a history. -/
def Zs (φB : LabelMap m) (H : History (Coord m)) (z : Address m) : Prop :=
  ∃ p ∈ H, S01 p.1 ∧ beta φB (yPart p.1) = z

def Good (s : Bool) (r : Sample m) : Prop :=
  ¬ Discovers r.1 r.2.1 (run A (hard r s) q []).1 ∧
  ∀ p ∈ (run A (hard r s) q []).1, S01 p.1 → NoWrap s (r.2.2 (beta r.2.1 (yPart p.1)))

/-- The static coupling: shift the table by `±2` on the slice-01 addresses of the run. -/
noncomputable def Psi (s : Bool) (r : Sample m) : Sample m := by
  classical
  exact (r.1, r.2.1, fun z =>
    if Zs r.2.1 (run A (hard r s) q []).1 z then r.2.2 z + shiftC s else r.2.2 z)

lemma theta_psi_in (s : Bool) (r : Sample m) (z : Address m)
    (hz : Zs r.2.1 (run A (hard r s) q []).1 z) (hw : NoWrap s (r.2.2 z)) :
    theta (Psi A q s r).2.2 z = theta r.2.2 z + (if s then 2 else -2) / 2 ^ dimension m := by
  simp only [Psi, theta, if_pos hz]
  rw [(noWrap_shift s _ hw).1]
  ring

lemma theta_psi_out (s : Bool) (r : Sample m) (z : Address m)
    (hz : ¬ Zs r.2.1 (run A (hard r s) q []).1 z) :
    theta (Psi A q s r).2.2 z = theta r.2.2 z := by
  simp only [Psi, theta, if_neg hz]

lemma psi_agree (s : Bool) (r : Sample m) (hg : Good A q s r) :
    ∀ p ∈ (run A (hard r s) q []).1, hard (Psi A q s r) (!s) p.1 = hard r s p.1 := by
  intro p hp
  have h1 : (Psi A q s r).1 = r.1 := rfl
  have h2 : (Psi A q s r).2.1 = r.2.1 := rfl
  by_cases hA : actionA ∈ p.1 <;> by_cases hB : actionB ∈ p.1
  · have hz : ¬ Zs r.2.1 (run A (hard r s) q []).1 (alpha r.1 (xPart p.1)) := by
      rintro ⟨p0, hp0, h01, hβ⟩
      exact hg.1 ⟨p0, hp0, p, hp, h01.1, h01.2, hA, hB, hβ.symm⟩
    simp only [hard, slice, hA, hB, decide_true, h1, theta_psi_out A q s r _ hz]
  · simp [hard, slice, hA, hB]
  · have hz : Zs r.2.1 (run A (hard r s) q []).1 (beta r.2.1 (yPart p.1)) :=
      ⟨p, hp, ⟨hA, hB⟩, rfl⟩
    have hw := hg.2 p hp ⟨hA, hB⟩
    simp only [hard, slice, hA, hB, decide_true, decide_false, h2,
      theta_psi_in A q s r _ hz hw]
    cases s <;> simp <;> ring
  · simp [hard, slice, hA, hB]

lemma psi_run (s : Bool) (r : Sample m) (hg : Good A q s r) :
    run A (hard (Psi A q s r) (!s)) q [] = run A (hard r s) q [] :=
  run_local A _ _ q [] (psi_agree A q s r hg)

lemma psi_good (s : Bool) (r : Sample m) (hg : Good A q s r) : Good A q (!s) (Psi A q s r) := by
  have e := psi_run A q s r hg
  have h1 : (Psi A q s r).1 = r.1 := rfl
  have h2 : (Psi A q s r).2.1 = r.2.1 := rfl
  refine ⟨?_, ?_⟩
  · rw [e, h1, h2]; exact hg.1
  · rw [e, h2]
    intro p hp h01
    have hz : Zs r.2.1 (run A (hard r s) q []).1 (beta r.2.1 (yPart p.1)) := ⟨p, hp, h01, rfl⟩
    simp only [Psi, if_pos hz]
    exact (noWrap_shift s _ (hg.2 p hp h01)).2

lemma psi_apply (s : Bool) (r : Sample m) (z : Address m) :
    (Psi A q s r).2.2 z = by
      classical
      exact if Zs r.2.1 (run A (hard r s) q []).1 z then r.2.2 z + shiftC s else r.2.2 z := rfl

lemma psi_inv (s : Bool) (r : Sample m) (hg : Good A q s r) :
    Psi A q (!s) (Psi A q s r) = r := by
  classical
  have e := psi_run A q s r hg
  have h2 : (Psi A q s r).2.1 = r.2.1 := rfl
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext z
  by_cases hz : Zs r.2.1 (run A (hard r s) q []).1 z
  · have hz' : Zs (Psi A q s r).2.1 (run A (hard (Psi A q s r) (!s)) q []).1 z := by
      rw [e, h2]; exact hz
    rw [psi_apply, if_pos hz', psi_apply, if_pos hz]
    exact shiftC_cancel s (r.2.2 z)
  · have hz' : ¬ Zs (Psi A q s r).2.1 (run A (hard (Psi A q s r) (!s)) q []).1 z := by
      rw [e, h2]; exact hz
    rw [psi_apply, if_neg hz', psi_apply, if_neg hz]

end Coupling

section Prob
variable {α : Type} [Fintype α] [Nonempty α]

lemma uP_congr (P Q : α → Prop) (h : ∀ a, P a ↔ Q a) : uniformProb P = uniformProb Q := by
  have : P = Q := funext fun a => propext (h a)
  subst this; rfl

lemma uP_nonneg (P : α → Prop) : 0 ≤ uniformProb P := by
  unfold uniformProb; positivity

lemma uP_mono (P Q : α → Prop) (h : ∀ a, P a → Q a) : uniformProb P ≤ uniformProb Q := by
  classical
  unfold uniformProb
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun a ha => by simp at ha ⊢; exact h a ha)

lemma uP_or (P Q : α → Prop) :
    uniformProb (fun a => P a ∨ Q a) ≤ uniformProb P + uniformProb Q := by
  classical
  unfold uniformProb
  rw [← add_div]
  gcongr
  exact_mod_cast (Finset.card_le_card (fun a ha => by simp at ha ⊢; exact ha)).trans
    (Finset.card_union_le _ _)

lemma uP_exists (E : ℕ → α → Prop) : ∀ q : ℕ,
    uniformProb (fun a => ∃ t < q, E t a) ≤ ∑ t ∈ Finset.range q, uniformProb (E t)
  | 0 => by simp [uniformProb]
  | q + 1 => by
    rw [Finset.sum_range_succ]
    calc uniformProb (fun a => ∃ t < q + 1, E t a)
        = uniformProb (fun a => (∃ t < q, E t a) ∨ E q a) := by
          apply uP_congr
          intro a
          constructor
          · rintro ⟨t, ht, h⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp ht with h' | h'
            · exact Or.inl ⟨t, h', h⟩
            · subst h'; exact Or.inr h
          · rintro (⟨t, ht, h⟩ | h)
            · exact ⟨t, by omega, h⟩
            · exact ⟨q, by omega, h⟩
      _ ≤ _ := uP_or _ _
      _ ≤ _ := by gcongr; exact uP_exists E q

lemma uP_split (P Q : α → Prop) :
    uniformProb P = uniformProb (fun a => P a ∧ Q a) + uniformProb (fun a => P a ∧ ¬ Q a) := by
  classical
  unfold uniformProb
  rw [← add_div]
  congr 1
  norm_cast
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext a; simp; tauto
  · exact Finset.disjoint_left.mpr (fun a ha hb => by simp at ha hb; exact hb.2 ha.2)

end Prob

section Resample
variable {m : ℕ}

lemma resample_card (E' : Sample m → Prop) (key : Sample m → Address m)
    (B : Finset (Fin (2 ^ dimension m))) (hB : B.card ≤ 2)
    (hkey : ∀ r v, E' r → key (upd r (key r) v) = key r)
    (S : Finset (Sample m)) (hS : ∀ r ∈ S, E' r ∧ r.2.2 (key r) ∈ B) :
    S.card * 2 ^ dimension m ≤ 2 * Fintype.card (Sample m) := by
  classical
  have hinj : (S ×ˢ (Finset.univ : Finset (Fin (2 ^ dimension m)))).card ≤
      ((Finset.univ : Finset (Sample m)) ×ˢ B).card := by
    apply Finset.card_le_card_of_injOn (fun x => (upd x.1 (key x.1) x.2, x.1.2.2 (key x.1)))
    · intro x hx
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, true_and,
        and_true] at hx ⊢
      exact (hS x.1 hx).2
    · rintro ⟨r, v⟩ hx ⟨r', v'⟩ hy hxy
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ,
        and_true] at hx hy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨h1, h2⟩ := hxy
      have hk : key r = key r' := by
        rw [← hkey r v (hS r hx).1, ← hkey r' v' (hS r' hy).1, h1]
      obtain ⟨a, b, θ⟩ := r
      obtain ⟨a', b', θ'⟩ := r'
      simp only [upd, Prod.mk.injEq] at h1 h2 hk ⊢
      obtain ⟨rfl, rfl, h3⟩ := h1
      rw [← hk] at h3 h2
      refine ⟨⟨rfl, rfl, ?_⟩, ?_⟩
      · funext z
        by_cases hz : z = key (a, b, θ)
        · subst hz; exact h2
        · have := congrFun h3 z
          simpa [Function.update_of_ne hz] using this
      · have := congrFun h3 (key (a, b, θ))
        simpa using this
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_univ] at hinj
  calc S.card * 2 ^ dimension m ≤ Fintype.card (Sample m) * B.card := hinj
    _ ≤ Fintype.card (Sample m) * 2 := Nat.mul_le_mul_left _ hB
    _ = 2 * Fintype.card (Sample m) := Nat.mul_comm _ _

lemma resample_prob (E' : Sample m → Prop) (key : Sample m → Address m)
    (B : Finset (Fin (2 ^ dimension m))) (hB : B.card ≤ 2)
    (hkey : ∀ r v, E' r → key (upd r (key r) v) = key r) :
    uniformProb (fun r => E' r ∧ r.2.2 (key r) ∈ B) ≤ 2 / 2 ^ dimension m := by
  classical
  unfold uniformProb
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  norm_cast
  apply resample_card E' key B hB hkey
  intro r hr; simpa using hr

end Resample

section Wrap
variable {m : ℕ} (A : Procedure (Coord m)) (q : ℕ)

/-- The slice-01 address of the `t`-th query (junk if there is none). -/
noncomputable def keyOf (s : Bool) (t : ℕ) (r : Sample m) : Address m :=
  match A (run A (hard r s) t []).1 with
  | Sum.inl _ => (fun _ => false, fun _ => false)
  | Sum.inr x => beta r.2.1 (yPart x)

/-- The `t`-th query is a slice-01 query whose address was not read before. -/
def Fresh (s : Bool) (t : ℕ) (r : Sample m) : Prop :=
  ∃ x, A (run A (hard r s) t []).1 = Sum.inr x ∧ S01 x ∧
    ∀ p ∈ (run A (hard r s) t []).1, ¬ Reads r.1 r.2.1 p.1 (beta r.2.1 (yPart x))

lemma keyOf_eq (s : Bool) (t : ℕ) (r : Sample m) (x : Cube (Coord m))
    (hx : A (run A (hard r s) t []).1 = Sum.inr x) : keyOf A s t r = beta r.2.1 (yPart x) := by
  unfold keyOf; rw [hx]

lemma fresh_key_inv (s : Bool) (t : ℕ) (r : Sample m) (v : Fin (2 ^ dimension m))
    (hr : Fresh A s t r) : keyOf A s t (upd r (keyOf A s t r) v) = keyOf A s t r := by
  obtain ⟨x, hx, _, hnr⟩ := hr
  have hk := keyOf_eq A s t r x hx
  have e : run A (hard (upd r (keyOf A s t r) v) s) t [] = run A (hard r s) t [] := by
    apply run_local
    intro p hp
    apply hard_upd
    rw [hk]; exact hnr p hp
  have hx' : A (run A (hard (upd r (keyOf A s t r) v) s) t []).1 = Sum.inr x := by
    rw [e]; exact hx
  rw [keyOf_eq A s t _ x hx', hk]
  rfl

noncomputable def BadSet (s : Bool) : Finset (Fin (2 ^ dimension m)) := by
  classical
  exact Finset.univ.filter (fun v => ¬ NoWrap s v)

lemma badSet_card (s : Bool) : (BadSet (m := m) s).card ≤ 2 := by
  classical
  have h4 := four_le_card (m := m)
  cases s
  · calc (BadSet (m := m) false).card ≤ (Finset.range 2).card := by
          apply Finset.card_le_card_of_injOn (fun v => v.val)
          · intro v hv
            simp only [BadSet, NoWrap, Finset.coe_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq, Bool.false_eq_true, if_false] at hv
            simp only [Finset.coe_range, Set.mem_Iio]; omega
          · intro v _ w _ h; exact Fin.ext h
      _ = 2 := by simp
  · calc (BadSet (m := m) true).card ≤ (Finset.range 2).card := by
          apply Finset.card_le_card_of_injOn (fun v => 2 ^ dimension m - 1 - v.val)
          · intro v hv
            simp only [BadSet, NoWrap, Finset.coe_filter, Finset.mem_univ, true_and,
              Set.mem_ofPred_eq, if_true] at hv
            have := v.isLt
            simp only [Finset.coe_range, Set.mem_Iio]; omega
          · intro v _ w _ h
            have := v.isLt; have := w.isLt
            simp only at h
            exact Fin.ext (by omega)
      _ = 2 := by simp

lemma not_good_cover (s : Bool) (r : Sample m) (hr : ¬ Good A q s r) :
    Discovers r.1 r.2.1 (run A (hard r s) q []).1 ∨
      ∃ t < q, Fresh A s t r ∧ r.2.2 (keyOf A s t r) ∈ BadSet s := by
  classical
  by_cases hD : Discovers r.1 r.2.1 (run A (hard r s) q []).1
  · exact Or.inl hD
  right
  have hex0 : ∃ p ∈ (run A (hard r s) q []).1, S01 p.1 ∧
      ¬ NoWrap s (r.2.2 (beta r.2.1 (yPart p.1))) := by
    by_contra hc
    exact hr ⟨hD, fun p hp h01 => by
      by_contra hw; exact hc ⟨p, hp, h01, hw⟩⟩
  obtain ⟨p, hp, h01, hbad⟩ := hex0
  set H := (run A (hard r s) q []).1 with hH
  set z := beta r.2.1 (yPart p.1) with hz
  have hex : ∃ j, ∃ hj : j < H.length, S01 H[j].1 ∧ beta r.2.1 (yPart H[j].1) = z := by
    obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
    exact ⟨j, hj, by rw [hpj]; exact ⟨h01, rfl⟩⟩
  obtain ⟨ht, h01t, hzt⟩ := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex,
      ¬ ∃ hj : j < H.length, S01 H[j].1 ∧ beta r.2.1 (yPart H[j].1) = z :=
    fun j hj => Nat.find_min hex hj
  have hlen : H.length ≤ q := by simpa using run_length_le A (hard r s) q []
  have htake : (run A (hard r s) (Nat.find hex) []).1 = H.take (Nat.find hex) := by
    simpa using run_take A (hard r s) (Nat.find hex) q [] (by omega)
  have hnext : A (H.take (Nat.find hex)) = Sum.inr H[Nat.find hex].1 :=
    run_next A (hard r s) q [] (Nat.find hex) (by simp) ht
  have hnext' : A (run A (hard r s) (Nat.find hex) []).1 = Sum.inr H[Nat.find hex].1 := by
    rw [htake]; exact hnext
  refine ⟨Nat.find hex, by omega, ⟨H[Nat.find hex].1, hnext', h01t, ?_⟩, ?_⟩
  · intro p' hp' hreads
    rw [htake] at hp'
    obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp'
    rw [List.length_take] at hj
    have hjt : j < Nat.find hex := by omega
    have hjH : j < H.length := by omega
    have hget : (H.take (Nat.find hex))[j] = H[j] := List.getElem_take
    rw [hzt] at hreads
    rcases hreads with ⟨h01', hβ'⟩ | ⟨h11', hα'⟩
    · exact hmin j hjt ⟨hjH, by rw [← hget, hpj]; exact ⟨h01', hβ'⟩⟩
    · exact hD ⟨p, hp, p', List.mem_of_mem_take hp', h01.1, h01.2, h11'.1, h11'.2, hα'⟩
  · rw [keyOf_eq A s _ r _ hnext', hzt]
    simp only [BadSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbad

lemma prob_fresh (s : Bool) (t : ℕ) :
    uniformProb (fun r : Sample m => Fresh A s t r ∧ r.2.2 (keyOf A s t r) ∈ BadSet s) ≤
      2 / 2 ^ dimension m :=
  resample_prob (Fresh A s t) (keyOf A s t) (BadSet s) (badSet_card s)
    (fun r v hr => fresh_key_inv A s t r v hr)

end Wrap

section Final
variable {m : ℕ} (A : Procedure (Coord m)) (q : ℕ)

lemma good_acc_eq :
    uniformProb (fun r : Sample m => (run A (hard r true) q []).2 = some true ∧ Good A q true r) =
    uniformProb (fun r : Sample m => (run A (hard r false) q []).2 = some true ∧
      Good A q false r) := by
  classical
  unfold uniformProb
  congr 2
  apply Finset.card_nbij' (Psi A q true) (Psi A q false)
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hr ⊢
    have e : run A (hard (Psi A q true r) false) q [] = run A (hard r true) q [] :=
      psi_run A q true r hr.2
    exact ⟨by rw [e]; exact hr.1, psi_good A q true r hr.2⟩
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hr ⊢
    have e : run A (hard (Psi A q false r) true) q [] = run A (hard r false) q [] :=
      psi_run A q false r hr.2
    exact ⟨by rw [e]; exact hr.1, psi_good A q false r hr.2⟩
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hr
    exact psi_inv A q true r hr.2
  · intro r hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hr
    exact psi_inv A q false r hr.2

lemma bad_le (hm : 1 ≤ m) (hbudget : Budget A q) (s : Bool) :
    uniformProb (fun r : Sample m => (run A (hard r s) q []).2 = some true ∧ ¬ Good A q s r) ≤
      (q : ℝ)^2 / 2^m + 2*(q : ℝ) / 2^(dimension m) := by
  have hdisc : uniformProb (fun r : Sample m => Discovers r.1 r.2.1 (run A (hard r s) q []).1) ≤
      (q : ℝ)^2 / 2^m := BarelyTestable.LowerBound.center_discovery hm A q hbudget s
  calc _ ≤ uniformProb (fun r : Sample m => ¬ Good A q s r) := uP_mono _ _ (fun r h => h.2)
    _ ≤ uniformProb (fun r : Sample m => Discovers r.1 r.2.1 (run A (hard r s) q []).1 ∨
          ∃ t < q, Fresh A s t r ∧ r.2.2 (keyOf A s t r) ∈ BadSet s) :=
        uP_mono _ _ (not_good_cover A q s)
    _ ≤ _ := uP_or _ _
    _ ≤ (q : ℝ)^2 / 2^m + ∑ _t ∈ Finset.range q, (2 : ℝ) / 2 ^ dimension m := by
        gcongr
        exact (uP_exists _ q).trans (Finset.sum_le_sum (fun t _ => prob_fresh A s t))
    _ = _ := by simp; ring

end Final

end BTHelper_indist

open BTHelper_indist in
theorem solution {m : ℕ} (hm : 1 ≤ m) (A : Procedure (Coord m))
    (q : ℕ) (hbudget : Budget A q) :
    |acceptanceProbability A true - acceptanceProbability A false| ≤
      (q : ℝ)^2 / 2^m + 2*(q : ℝ) / 2^(dimension m) := by
  have hacc : ∀ s, acceptanceProbability A s =
      uniformProb (fun r : Sample m => (run A (hard r s) q []).2 = some true) :=
    fun s => uP_congr _ _ (fun r => accepts_iff A _ q hbudget)
  have s1 := uP_split (fun r : Sample m => (run A (hard r true) q []).2 = some true)
    (Good A q true)
  have s2 := uP_split (fun r : Sample m => (run A (hard r false) q []).2 = some true)
    (Good A q false)
  have e := good_acc_eq A q
  rw [hacc, hacc]
  have h1 := bad_le A q hm hbudget true
  have h2 := bad_le A q hm hbudget false
  have h3 := uP_nonneg (fun r : Sample m => (run A (hard r true) q []).2 = some true ∧
    ¬ Good A q true r)
  have h4 := uP_nonneg (fun r : Sample m => (run A (hard r false) q []).2 = some true ∧
    ¬ Good A q false r)
  rw [abs_sub_le_iff]
  constructor <;> linarith
