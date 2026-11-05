-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T16:53:40.639384+00:00
-- url     : https://prove2.me/submissions/fcfc0d95-acfb-422f-8252-7d5ee9a1bdbe

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_corollary_1

open CostSharingPNE.Char

namespace CSPLemma9Aux

variable {n : ℕ}

/-! ### Games with integer resource multiplicities and several welfare functions -/

/-- Players on resource `r` for a profile over an arbitrary resource type. -/
def pl {R : Type} [DecidableEq R] (a : Fin n → Finset R) (r : R) : Finset (Fin n) :=
  Finset.univ.filter (fun k => r ∈ a k)

lemma guarantees_mono {𝕎 𝕍 : Set (Welfare n)} (f : Welfare n → Rule n) (h : 𝕍 ⊆ 𝕎)
    (hpne : GuaranteesPNE 𝕎 f) : GuaranteesPNE 𝕍 f :=
  fun m hm W hW A hA => hpne m hm W (fun r => h (hW r)) A hA

/-- A game whose resource `r` carries the welfare function `Wl r ∈ 𝕎` and comes with `v r`
identical copies (the scaling coefficients `v_r` of Appendix A, p. 17). -/
lemma weighted_pne (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f)
    (w0 : Welfare n) (hw0 : w0 ∈ 𝕎)
    {R : Type} [Fintype R] [DecidableEq R] (Wl : R → Welfare n) (hWl : ∀ r, Wl r ∈ 𝕎)
    (v : R → ℕ) (A : Fin n → Finset (Finset R)) (hA : ∀ k, (A k).Nonempty) :
    ∃ a : Fin n → Finset R, (∀ k, a k ∈ A k) ∧ ∀ k, ∀ b ∈ A k,
      ∑ r ∈ b, (v r : ℝ) * f (Wl r) k (pl (Function.update a k b) r) ≤
        ∑ r ∈ a k, (v r : ℝ) * f (Wl r) k (pl a r) := by
  classical
  let C := (Σ r : R, Fin (v r)) ⊕ Fin 2
  let m := Fintype.card C
  have hm : 1 < m := by
    show 1 < Fintype.card ((Σ r : R, Fin (v r)) ⊕ Fin 2)
    rw [Fintype.card_sum]; simp
  let e : C ≃ Fin m := Fintype.equivFin C
  let WC : C → Welfare n := fun c => Sum.elim (fun x => Wl x.1) (fun _ => w0) c
  let Wm : Fin m → Welfare n := fun x => WC (e.symm x)
  have hWm : ∀ x, Wm x ∈ 𝕎 := by
    intro x
    simp only [Wm, WC]
    cases e.symm x with
    | inl y => exact hWl y.1
    | inr _ => exact hw0
  let inlE : (Σ r : R, Fin (v r)) ↪ C := ⟨Sum.inl, Sum.inl_injective⟩
  let lift : Finset R → Finset (Fin m) := fun s =>
    ((s.sigma (fun r => (Finset.univ : Finset (Fin (v r))))).map inlE).map e.toEmbedding
  let A' : Fin n → Finset (Finset (Fin m)) := fun k => (A k).image lift
  have hA' : ∀ k, (A' k).Nonempty := fun k => (hA k).image _
  obtain ⟨a', ha', hN⟩ := hpne m hm Wm hWm A' hA'
  have hpre : ∀ k, ∃ s ∈ A k, lift s = a' k := by
    intro k
    have := ha' k
    simp only [A', Finset.mem_image] at this
    exact this
  choose a ha hla using hpre
  have ha'eq : a' = fun k => lift (a k) := by funext k; exact (hla k).symm
  have hU : ∀ (b : Fin n → Finset R) (k : Fin n),
      utility Wm f (fun k => lift (b k)) k =
        ∑ r ∈ b k, (v r : ℝ) * f (Wl r) k (pl b r) := by
    intro b k
    unfold utility
    have hpl : ∀ (r : R) (t : Fin (v r)),
        players (fun k => lift (b k)) (e (Sum.inl ⟨r, t⟩)) = pl b r := by
      intro r t; ext k'; simp [players, pl, lift, inlE]
    have hW : ∀ (r : R) (t : Fin (v r)), Wm (e (Sum.inl ⟨r, t⟩)) = Wl r := by
      intro r t; simp [Wm, WC]
    simp only [lift, Finset.sum_map]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro r _
    have h2 : ∀ t : Fin (v r), f (Wm (e (Sum.inl ⟨r, t⟩))) k
        (players (fun k => lift (b k)) (e (Sum.inl ⟨r, t⟩))) = f (Wl r) k (pl b r) :=
      fun t => by rw [hpl r t, hW r t]
    refine (Finset.sum_congr rfl (fun t _ => h2 t)).trans ?_
    simp
  refine ⟨a, ha, fun k b hb => ?_⟩
  have hdev := hN k (lift b) (Finset.mem_image_of_mem lift hb)
  have hupd : Function.update a' k (lift b) = fun k' => lift (Function.update a k b k') := by
    funext k'
    by_cases hk : k' = k
    · subst hk; simp
    · rw [Function.update_of_ne hk, Function.update_of_ne hk, ha'eq]
  rw [hupd, ha'eq, hU, hU] at hdev
  simpa using hdev

/-! ### The 2 × 2 box game isolating basis shares (Counterexamples 4–5) -/

section Box

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (St : ι → Finset (Fin n)) (z : ι → ℤ) (i j : Fin n)

/-- Resources `r_1^t` (`b = 0`, top row) and `r_2^t` (`b = 1`, bottom row) for `t ∈ ι`. -/
abbrev Res (ι : Type) := ι × Fin 2

def vw (r : Res ι) : ℕ := (z r.1).natAbs

def topB (r : Res ι) : Bool := decide (r.2 = 0 ∧ i ∈ St r.1)
def botB (r : Res ι) : Bool := decide (r.2 = 1 ∧ i ∈ St r.1)
def lftB (r : Res ι) : Bool :=
  decide (j ∈ St r.1 ∧ ((r.2 = 0 ∧ z r.1 < 0) ∨ (r.2 = 1 ∧ 0 < z r.1)))
def rgtB (r : Res ι) : Bool :=
  decide (j ∈ St r.1 ∧ ((r.2 = 0 ∧ 0 < z r.1) ∨ (r.2 = 1 ∧ z r.1 < 0)))
def fixB (k : Fin n) (r : Res ι) : Bool := decide (k ∈ St r.1)

def act (B : Res ι → Bool) : Finset (Res ι) := Finset.univ.filter (fun r => B r = true)

lemma mem_act (B : Res ι → Bool) (r : Res ι) : r ∈ act B ↔ B r = true := by simp [act]

variable (Wl : ι → Welfare n) (f : Welfare n → Rule n)

/-- Share of player `p` on resource `r` when the other strategic player `q` is present iff
`X r`. -/
noncomputable def Fsh (p q : Fin n) (X : Res ι → Bool) (r : Res ι) : ℝ :=
  (vw z r : ℝ) * f (Wl r.1) p (if X r = true then St r.1 else (St r.1).erase q)

lemma sum_res (F : Res ι → ℝ) : ∑ r, F r = ∑ t, (F (t, 0) + F (t, 1)) := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]

lemma natAbs_neg' (x : ℤ) (hx : x < 0) : ((x.natAbs : ℕ) : ℝ) = -(x : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hx)]

lemma natAbs_pos' (x : ℤ) (hx : 0 < x) : ((x.natAbs : ℕ) : ℝ) = (x : ℝ) := by
  rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hx)]

lemma ite_erase (T : Finset (Fin n)) (x : Fin n) :
    (if x ∈ T then T else T.erase x) = T := by
  split_ifs with h
  · rfl
  · exact Finset.erase_eq_of_notMem h

lemma fin2_ne : ¬ ((0 : Fin 2) = 1) := by decide
lemma fin2_ne' : ¬ ((1 : Fin 2) = 0) := by decide

/-- `j`'s gain at `Top` from `L` to `R`. -/
lemma Kj_top (hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i)) :
    ∑ r ∈ act (rgtB St z j), Fsh St z Wl f j i (topB St i) r -
      ∑ r ∈ act (lftB St z j), Fsh St z Wl f j i (topB St i) r =
    ∑ t, (z t : ℝ) * (f (Wl t) j (St t) - f (Wl t) j ((St t).erase i)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res]
  apply Finset.sum_congr rfl
  intro t _
  simp only [rgtB, lftB, topB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq, ite_erase]
  by_cases hj : j ∈ St t
  · rcases lt_trichotomy (z t) 0 with hz | hz | hz
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
    · simp [hz]
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
  · simp [hj, hjout t hj]

/-- `j`'s gain at `Bottom` from `L` to `R`. -/
lemma Kj_bot (hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i)) :
    ∑ r ∈ act (rgtB St z j), Fsh St z Wl f j i (botB St i) r -
      ∑ r ∈ act (lftB St z j), Fsh St z Wl f j i (botB St i) r =
    -∑ t, (z t : ℝ) * (f (Wl t) j (St t) - f (Wl t) j ((St t).erase i)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [rgtB, lftB, botB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq, ite_erase]
  by_cases hj : j ∈ St t
  · rcases lt_trichotomy (z t) 0 with hz | hz | hz
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
    · simp [hz]
    · simp [hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
  · simp [hj, hjout t hj]

/-- `i`'s gain against `R` from `T` to `B`. -/
lemma Ki_rgt (hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j)) :
    ∑ r ∈ act (botB St i), Fsh St z Wl f i j (rgtB St z j) r -
      ∑ r ∈ act (topB St i), Fsh St z Wl f i j (rgtB St z j) r =
    -∑ t, (z t : ℝ) * (f (Wl t) i (St t) - f (Wl t) i ((St t).erase j)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t _
  simp only [rgtB, botB, topB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq]
  by_cases hi : i ∈ St t
  · by_cases hj : j ∈ St t
    · rcases lt_trichotomy (z t) 0 with hz | hz | hz
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
      · simp [hz]
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
    · simp [hi, hj, Finset.erase_eq_of_notMem hj]
  · simp [hi, hiout t hi]

/-- `i`'s gain against `L` from `T` to `B`. -/
lemma Ki_lft (hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j)) :
    ∑ r ∈ act (botB St i), Fsh St z Wl f i j (lftB St z j) r -
      ∑ r ∈ act (topB St i), Fsh St z Wl f i j (lftB St z j) r =
    ∑ t, (z t : ℝ) * (f (Wl t) i (St t) - f (Wl t) i ((St t).erase j)) := by
  unfold act
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, sum_res]
  apply Finset.sum_congr rfl
  intro t _
  simp only [lftB, botB, topB, Fsh, vw, fin2_ne, fin2_ne', true_and, false_and,
    and_false, or_false, false_or, decide_eq_true_eq]
  by_cases hi : i ∈ St t
  · by_cases hj : j ∈ St t
    · rcases lt_trichotomy (z t) 0 with hz | hz | hz
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_neg' _ hz]; ring
      · simp [hz]
      · simp [hi, hj, hz, not_lt.mpr hz.le, natAbs_pos' _ hz]; ring
    · simp [hi, hj, Finset.erase_eq_of_notMem hj]
  · simp [hi, hiout t hi]

end Box

open Classical in
/-- Players on a resource of the box game. -/
lemma pl_box {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (b : Fin n → Finset (Res ι))
    (hbi : ∀ r ∈ b i, i ∈ St r.1) (hbj : ∀ r ∈ b j, j ∈ St r.1)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) (r : Res ι) :
    pl b r = (St r.1).filter (fun k => (k = i → r ∈ b i) ∧ (k = j → r ∈ b j)) := by
  ext k
  simp only [pl, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hki : k = i
  · subst hki
    constructor
    · intro h; exact ⟨hbi r h, fun _ => h, fun h' => absurd h' hij⟩
    · rintro ⟨-, h, -⟩; exact h rfl
  by_cases hkj : k = j
  · subst hkj
    constructor
    · intro h; exact ⟨hbj r h, fun h' => absurd h' hki, fun _ => h⟩
    · rintro ⟨-, -, h⟩; exact h rfl
  rw [hfix k hki hkj, mem_act]
  simp [fixB, hki, hkj]

lemma pl_box_j {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (b : Fin n → Finset (Res ι))
    (hbi : ∀ r ∈ b i, i ∈ St r.1) (hbj : ∀ r ∈ b j, j ∈ St r.1)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) (r : Res ι) (hr : r ∈ b j) :
    pl b r = if r ∈ b i then St r.1 else (St r.1).erase i := by
  rw [pl_box St i j hij b hbi hbj hfix r]
  ext k
  by_cases h : r ∈ b i
  · simp only [h, if_true, Finset.mem_filter]
    constructor
    · exact fun h' => h'.1
    · intro hk; exact ⟨hk, fun _ => trivial, fun _ => hr⟩
  · simp only [h, if_false, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hk, h1, -⟩; exact ⟨h1, hk⟩
    · rintro ⟨hki, hk⟩; exact ⟨hk, fun h' => absurd h' hki, fun _ => hr⟩

lemma pl_box_i {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (i j : Fin n)
    (hij : i ≠ j) (b : Fin n → Finset (Res ι))
    (hbi : ∀ r ∈ b i, i ∈ St r.1) (hbj : ∀ r ∈ b j, j ∈ St r.1)
    (hfix : ∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) (r : Res ι) (hr : r ∈ b i) :
    pl b r = if r ∈ b j then St r.1 else (St r.1).erase j := by
  rw [pl_box St i j hij b hbi hbj hfix r]
  ext k
  by_cases h : r ∈ b j
  · simp only [h, if_true, Finset.mem_filter]
    constructor
    · exact fun h' => h'.1
    · intro hk; exact ⟨hk, fun _ => hr, fun _ => trivial⟩
  · simp only [h, if_false, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hk, -, h1⟩; exact ⟨h1, hk⟩
    · rintro ⟨hkj, hk⟩; exact ⟨hk, fun _ => hr, fun h' => absurd h' hkj⟩

/-- The box game has a best-response cycle `TL → TR → BR → BL → TL` as soon as both
strategic players' gains are positive. -/
lemma box_cycle (𝕎 : Set (Welfare n)) (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f)
    (w0 : Welfare n) (hw0 : w0 ∈ 𝕎)
    {ι : Type} [Fintype ι] [DecidableEq ι] (St : ι → Finset (Fin n)) (z : ι → ℤ)
    (Wl : ι → Welfare n) (hWl : ∀ t, Wl t ∈ 𝕎) (i j : Fin n) (hij : i ≠ j)
    (hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i))
    (hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j))
    (hJ : 0 < ∑ t, (z t : ℝ) * (f (Wl t) j (St t) - f (Wl t) j ((St t).erase i)))
    (hI : 0 < -∑ t, (z t : ℝ) * (f (Wl t) i (St t) - f (Wl t) i ((St t).erase j))) :
    False := by
  classical
  let A : Fin n → Finset (Finset (Res ι)) := fun k =>
    if k = i then {act (topB St i), act (botB St i)}
    else if k = j then {act (lftB St z j), act (rgtB St z j)}
    else {act (fixB St k)}
  have hA : ∀ k, (A k).Nonempty := by
    intro k; simp only [A]; split_ifs <;> simp
  obtain ⟨a, ha, hN⟩ := weighted_pne 𝕎 f hpne w0 hw0 (fun r : Res ι => Wl r.1)
    (fun r => hWl r.1) (vw z) A hA
  have hai := ha i
  have haj := ha j
  simp only [A, if_true, if_neg (Ne.symm hij), Finset.mem_insert, Finset.mem_singleton] at hai haj
  have hfix : ∀ k, k ≠ i → k ≠ j → a k = act (fixB St k) := by
    intro k hki hkj
    have := ha k
    simp only [A, hki, hkj, if_false, Finset.mem_singleton] at this
    exact this
  have bT : ∀ r ∈ act (topB St i), i ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [topB, decide_eq_true_eq] at hr; exact hr.2
  have bB : ∀ r ∈ act (botB St i), i ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [botB, decide_eq_true_eq] at hr; exact hr.2
  have bL : ∀ r ∈ act (lftB St z j), j ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [lftB, decide_eq_true_eq] at hr; exact hr.1
  have bR : ∀ r ∈ act (rgtB St z j), j ∈ St r.1 := by
    intro r hr; rw [mem_act] at hr; simp only [rgtB, decide_eq_true_eq] at hr; exact hr.1
  have Uj : ∀ (b : Fin n → Finset (Res ι)) (X Y : Res ι → Bool),
      b i = act X → b j = act Y → (∀ r ∈ act X, i ∈ St r.1) → (∀ r ∈ act Y, j ∈ St r.1) →
      (∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) →
      ∑ r ∈ act Y, (vw z r : ℝ) * f (Wl r.1) j (pl b r) = ∑ r ∈ act Y, Fsh St z Wl f j i X r := by
    intro b X Y hbX hbY hX hY hbf
    apply Finset.sum_congr rfl
    intro r hr
    rw [pl_box_j St i j hij b (hbX ▸ hX) (hbY ▸ hY) hbf r (hbY ▸ hr)]
    simp only [Fsh, hbX, mem_act]
  have Ui : ∀ (b : Fin n → Finset (Res ι)) (X Y : Res ι → Bool),
      b i = act X → b j = act Y → (∀ r ∈ act X, i ∈ St r.1) → (∀ r ∈ act Y, j ∈ St r.1) →
      (∀ k, k ≠ i → k ≠ j → b k = act (fixB St k)) →
      ∑ r ∈ act X, (vw z r : ℝ) * f (Wl r.1) i (pl b r) = ∑ r ∈ act X, Fsh St z Wl f i j Y r := by
    intro b X Y hbX hbY hX hY hbf
    apply Finset.sum_congr rfl
    intro r hr
    rw [pl_box_i St i j hij b (hbX ▸ hX) (hbY ▸ hY) hbf r (hbX ▸ hr)]
    simp only [Fsh, hbY, mem_act]
  have updj : ∀ Y : Res ι → Bool, ∀ k, k ≠ i → k ≠ j →
      Function.update a j (act Y) k = act (fixB St k) := by
    intro Y k h1 h2; rw [Function.update_of_ne h2]; exact hfix k h1 h2
  have updi : ∀ X : Res ι → Bool, ∀ k, k ≠ i → k ≠ j →
      Function.update a i (act X) k = act (fixB St k) := by
    intro X k h1 h2; rw [Function.update_of_ne h1]; exact hfix k h1 h2
  have Kjt := Kj_top St z i j Wl f hjout
  have Kjb := Kj_bot St z i j Wl f hjout
  have Kir := Ki_rgt St z i j Wl f hiout
  have Kil := Ki_lft St z i j Wl f hiout
  have uji : Function.update a j (act (rgtB St z j)) i = a i := Function.update_of_ne hij _ _
  have uji' : Function.update a j (act (lftB St z j)) i = a i := Function.update_of_ne hij _ _
  have uij : Function.update a i (act (botB St i)) j = a j :=
    Function.update_of_ne (Ne.symm hij) _ _
  have uij' : Function.update a i (act (topB St i)) j = a j :=
    Function.update_of_ne (Ne.symm hij) _ _
  rcases hai with hai | hai <;> rcases haj with haj | haj
  · have hdev := hN j _ (show act (rgtB St z j) ∈ A j by simp [A, Ne.symm hij])
    rw [haj, Uj _ (topB St i) (rgtB St z j) (uji.trans hai) (by simp) bT bR (updj _),
      Uj a (topB St i) (lftB St z j) hai haj bT bL hfix] at hdev
    linarith
  · have hdev := hN i _ (show act (botB St i) ∈ A i by simp [A])
    rw [hai, Ui _ (botB St i) (rgtB St z j) (by simp) (uij.trans haj) bB bR (updi _),
      Ui a (topB St i) (rgtB St z j) hai haj bT bR hfix] at hdev
    linarith
  · have hdev := hN i _ (show act (topB St i) ∈ A i by simp [A])
    rw [hai, Ui _ (topB St i) (lftB St z j) (by simp) (uij'.trans haj) bT bL (updi _),
      Ui a (botB St i) (lftB St z j) hai haj bB bL hfix] at hdev
    linarith
  · have hdev := hN j _ (show act (lftB St z j) ∈ A j by simp [A, Ne.symm hij])
    rw [haj, Uj _ (botB St i) (lftB St z j) (uji'.trans hai) (by simp) bB bL (updj _),
      Uj a (botB St i) (rgtB St z j) hai haj bB bR hfix] at hdev
    linarith

lemma frac_bound (e y : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) : -|y| ≤ e * y ∧ e * y ≤ |y| := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy]; constructor <;> nlinarith
  · rw [abs_of_nonpos hy]; constructor <;> nlinarith

/-- If `x` and `y` are linearly independent in `ℝ²`, an integer vector `u` has `u·y > 0 > u·x`. -/
lemma int_sol (x1 x2 y1 y2 : ℝ) (hD : x1 * y2 - x2 * y1 ≠ 0) :
    ∃ u1 u2 : ℤ, 0 < (u1 : ℝ) * y1 + u2 * y2 ∧ (u1 : ℝ) * x1 + u2 * x2 < 0 := by
  set D := x1 * y2 - x2 * y1 with hDdef
  set a1 := -(x2 + y2) / D
  set a2 := (x1 + y1) / D
  have hax : a1 * x1 + a2 * x2 = -1 := by
    simp only [a1, a2]; field_simp; rw [hDdef]; ring
  have hay : a1 * y1 + a2 * y2 = 1 := by
    simp only [a1, a2]; field_simp; rw [hDdef]; ring
  obtain ⟨N, hN⟩ := exists_nat_gt (|x1| + |x2| + |y1| + |y2|)
  refine ⟨⌊(N : ℝ) * a1⌋, ⌊(N : ℝ) * a2⌋, ?_, ?_⟩
  · set e1 := (N : ℝ) * a1 - ⌊(N : ℝ) * a1⌋
    set e2 := (N : ℝ) * a2 - ⌊(N : ℝ) * a2⌋
    have h1 := frac_bound e1 y1 (by simp [e1, Int.floor_le]) (by
      simp only [e1]; linarith [Int.lt_floor_add_one ((N : ℝ) * a1)])
    have h2 := frac_bound e2 y2 (by simp [e2, Int.floor_le]) (by
      simp only [e2]; linarith [Int.lt_floor_add_one ((N : ℝ) * a2)])
    have : (⌊(N : ℝ) * a1⌋ : ℝ) * y1 + ⌊(N : ℝ) * a2⌋ * y2 = N * (a1 * y1 + a2 * y2) -
        (e1 * y1 + e2 * y2) := by simp only [e1, e2]; ring
    rw [this, hay]
    have := abs_nonneg x1; have := abs_nonneg x2
    linarith
  · set e1 := (N : ℝ) * a1 - ⌊(N : ℝ) * a1⌋
    set e2 := (N : ℝ) * a2 - ⌊(N : ℝ) * a2⌋
    have h1 := frac_bound e1 x1 (by simp [e1, Int.floor_le]) (by
      simp only [e1]; linarith [Int.lt_floor_add_one ((N : ℝ) * a1)])
    have h2 := frac_bound e2 x2 (by simp [e2, Int.floor_le]) (by
      simp only [e2]; linarith [Int.lt_floor_add_one ((N : ℝ) * a2)])
    have : (⌊(N : ℝ) * a1⌋ : ℝ) * x1 + ⌊(N : ℝ) * a2⌋ * x2 = N * (a1 * x1 + a2 * x2) -
        (e1 * x1 + e2 * x2) := by simp only [e1, e2]; ring
    rw [this, hax]
    have := abs_nonneg y1; have := abs_nonneg y2
    linarith

end CSPLemma9Aux

open CSPLemma9Aux in
theorem solution (n : ℕ) (hn : 1 < n) (W₁ W₂ : Welfare n) (f : Welfare n → Rule n)
    (hbb₁ : IsBudgetBalanced (f W₁) W₁) (hbb₂ : IsBudgetBalanced (f W₂) W₂)
    (h0₁ : ∀ i S, i ∉ S → f W₁ i S = 0) (h0₂ : ∀ i S, i ∉ S → f W₂ i S = 0)
    (hpne : GuaranteesPNE {W₁, W₂} f) :
    ∀ i j : Fin n, ∀ T' ∈ coalitionsPair W₁ i j, ∀ T ∈ coalitionsPair W₂ i j,
      basisRule (f W₁) W₁ T' i T' * basisRule (f W₂) W₂ T j T =
        basisRule (f W₂) W₂ T i T * basisRule (f W₁) W₁ T' j T' := by
  intro i j T' hT' T hT
  unfold coalitionsPair at hT' hT
  rw [Finset.mem_filter] at hT' hT
  obtain ⟨hc1, hi1, hj1⟩ := hT'
  obtain ⟨hc2, hi2, hj2⟩ := hT
  by_cases hij : i = j
  · subst hij; ring
  by_contra hne
  have hq1 : mobius W₁ T' ≠ 0 := by
    unfold coalitions at hc1; exact (Finset.mem_filter.mp hc1).2.2
  have hq2 : mobius W₂ T ≠ 0 := by
    unfold coalitions at hc2; exact (Finset.mem_filter.mp hc2).2.2
  set B1 : Fin n → ℝ := fun x => basisRule (f W₁) W₁ T' x T' with hB1
  set B2 : Fin n → ℝ := fun x => basisRule (f W₂) W₂ T x T with hB2
  have hD : (mobius W₁ T' * B1 i) * (mobius W₂ T * B2 j) -
      (mobius W₂ T * B2 i) * (mobius W₁ T' * B1 j) ≠ 0 := by
    have : (mobius W₁ T' * B1 i) * (mobius W₂ T * B2 j) -
        (mobius W₂ T * B2 i) * (mobius W₁ T' * B1 j) =
        (mobius W₁ T' * mobius W₂ T) * (B1 i * B2 j - B2 i * B1 j) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hq1 hq2) (sub_ne_zero.mpr hne)
  obtain ⟨u1, u2, hy, hx⟩ := int_sol _ _ _ _ hD
  have hp1 : GuaranteesPNE {W₁} f :=
    guarantees_mono f (by intro W hW; rw [Set.mem_singleton_iff] at hW; simp [hW]) hpne
  have hp2 : GuaranteesPNE {W₂} f :=
    guarantees_mono f (by intro W hW; rw [Set.mem_singleton_iff] at hW; simp [hW]) hpne
  obtain ⟨c1, h49₁, h50₁⟩ := corollary_1 n hn W₁ f hbb₁ hp1 h0₁ T' hc1
  obtain ⟨c2, h49₂, h50₂⟩ := corollary_1 n hn W₂ f hbb₂ hp2 h0₂ T hc2
  let ι := {T'' // T'' ∈ coalitionsIn W₁ T'} ⊕ {T'' // T'' ∈ coalitionsIn W₂ T}
  let St : ι → Finset (Fin n) := Sum.elim (fun t => t.1) (fun t => t.1)
  let Wl : ι → Welfare n := Sum.elim (fun _ => W₁) (fun _ => W₂)
  let z : ι → ℤ := Sum.elim (fun t => u1 * c1 t.1) (fun t => u2 * c2 t.1)
  have hWl : ∀ t, Wl t ∈ ({W₁, W₂} : Set (Welfare n)) := by
    intro t
    cases t with
    | inl _ => simp [Wl]
    | inr _ => simp [Wl]
  have key : ∀ x p : Fin n, x ∈ T' → x ∈ T → p ∈ T' → p ∈ T → p ≠ x →
      ∑ t, (z t : ℝ) * (f (Wl t) x (St t) - f (Wl t) x ((St t).erase p)) =
        u1 * (mobius W₁ T' * B1 x) + u2 * (mobius W₂ T * B2 x) := by
    intro x p hx1 hx2 hp1' hp2' hpx
    rw [Fintype.sum_sum_type]
    simp only [St, Wl, z, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_coe_sort (coalitionsIn W₁ T') (fun T'' => ((u1 * c1 T'' : ℤ) : ℝ) *
        (f W₁ x T'' - f W₁ x (T''.erase p))),
      Finset.sum_coe_sort (coalitionsIn W₂ T) (fun T'' => ((u2 * c2 T'' : ℤ) : ℝ) *
        (f W₂ x T'' - f W₂ x (T''.erase p)))]
    have e1 : ∑ T'' ∈ coalitionsIn W₁ T', ((u1 * c1 T'' : ℤ) : ℝ) *
        (f W₁ x T'' - f W₁ x (T''.erase p)) = u1 * (∑ T'' ∈ coalitionsIn W₁ T',
          (c1 T'' : ℝ) * f W₁ x T'' - ∑ T'' ∈ coalitionsIn W₁ T', (c1 T'' : ℝ) *
            f W₁ x (T''.erase p)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro _ _; push_cast; ring
    have e2 : ∑ T'' ∈ coalitionsIn W₂ T, ((u2 * c2 T'' : ℤ) : ℝ) *
        (f W₂ x T'' - f W₂ x (T''.erase p)) = u2 * (∑ T'' ∈ coalitionsIn W₂ T,
          (c2 T'' : ℝ) * f W₂ x T'' - ∑ T'' ∈ coalitionsIn W₂ T, (c2 T'' : ℝ) *
            f W₂ x (T''.erase p)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro _ _; push_cast; ring
    rw [e1, e2, ← h49₁ x hx1, ← h49₂ x hx2, ← (h50₁ x hx1 p hp1' hpx).2,
      ← (h50₁ x hx1 p hp1' hpx).1, ← (h50₂ x hx2 p hp2' hpx).2, ← (h50₂ x hx2 p hp2' hpx).1]
    simp only [B1, B2]
    ring
  have hjout : ∀ t, j ∉ St t → f (Wl t) j (St t) = f (Wl t) j ((St t).erase i) := by
    intro t ht
    cases t with
    | inl t =>
      simp only [St, Wl, Sum.elim_inl] at ht ⊢
      rw [h0₁ j _ ht, h0₁ j _ (fun h => ht (Finset.mem_of_mem_erase h))]
    | inr t =>
      simp only [St, Wl, Sum.elim_inr] at ht ⊢
      rw [h0₂ j _ ht, h0₂ j _ (fun h => ht (Finset.mem_of_mem_erase h))]
  have hiout : ∀ t, i ∉ St t → f (Wl t) i (St t) = f (Wl t) i ((St t).erase j) := by
    intro t ht
    cases t with
    | inl t =>
      simp only [St, Wl, Sum.elim_inl] at ht ⊢
      rw [h0₁ i _ ht, h0₁ i _ (fun h => ht (Finset.mem_of_mem_erase h))]
    | inr t =>
      simp only [St, Wl, Sum.elim_inr] at ht ⊢
      rw [h0₂ i _ ht, h0₂ i _ (fun h => ht (Finset.mem_of_mem_erase h))]
  apply box_cycle {W₁, W₂} f hpne W₁ (by simp) St z Wl hWl i j hij hjout hiout
  · rw [key j i hj1 hj2 hi1 hi2 hij]
    linarith
  · rw [key i j hi1 hi2 hj1 hj2 (Ne.symm hij)]
    linarith
