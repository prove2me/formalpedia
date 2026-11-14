-- Prove2me | solution 1 for CostSharingPNE.Char.lemma_10
-- status  : ACCEPTED   (prove)
-- author  : @Albert
-- created : 2026-11-13T15:29:01.514947+00:00
-- url     : https://prove2.me/submissions/10bf32c5-8453-4e9d-9784-22d5a7c8eb3d

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem
import Definitions.Def_CostSharingPNE_Char_Basis
import Theorems.Thm_CostSharingPNE_Char_corollary_1
import Theorems.Thm_CostSharingPNE_Char_lemma_8
import Theorems.Thm_CostSharingPNE_Char_lemma_9

open CostSharingPNE.Char

namespace CostSharingIndexedAux

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

end CostSharingIndexedAux


namespace ShapleyBinaryCycle

/-- On an odd cycle of desired flips, a player must violate its desired relation
with its successor. The statement permits any cycle length and any pattern of flips. -/
theorem exists_mismatch {k : ℕ} {flip : Fin k → Bool} (hflip : ∏ l, (if flip l then (-1 : ℝ) else 1) = -1)
    (a : Fin k → Bool) :
    ∃ l, a l ≠ (a (finRotate k l) ^^ flip l) := by
  classical
  by_contra! h
  let sign : Bool → ℝ := fun b => if b then -1 else 1
  have hs (l : Fin k) : sign (a l) = sign (a (finRotate k l)) * sign (flip l) := by
    rw [h l]
    cases a (finRotate k l) <;> cases flip l <;> norm_num [sign]
  have hprod := congrArg (fun g : Fin k → ℝ => ∏ l, g l) (funext hs)
  simp only [Finset.prod_mul_distrib] at hprod
  have hrot : (∏ l, sign (a (finRotate k l))) = ∏ l, sign (a l) :=
    Equiv.prod_comp (finRotate k) (sign ∘ a)
  have hnon : (∏ l, sign (a l)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
    (fun l _ => by cases a l <;> norm_num [sign])
  change (∏ l, sign (flip l)) = -1 at hflip
  rw [hrot,hflip,mul_neg_one] at hprod
  exact hnon (by linarith)

theorem no_binary_equilibrium {k : ℕ} {flip : Fin k → Bool}
    (hflip : ∏ l, (if flip l then (-1 : ℝ) else 1) = -1)
    (payoff : (Fin k → Bool) → Fin k → ℝ)
    (improves : ∀ (a : Fin k → Bool) l, a l ≠ (a (finRotate k l) ^^ flip l) →
      payoff a l < payoff (Function.update a l (!a l)) l) :
    ¬ ∃ a, ∀ l b, payoff (Function.update a l b) l ≤ payoff a l := by
  rintro ⟨a,he⟩
  obtain ⟨l,hl⟩ := exists_mismatch hflip a
  exact (not_lt_of_ge (he l (!a l))) (improves a l hl)

end ShapleyBinaryCycle

namespace ShapleyBinaryCycle

/-- If the outgoing edge has larger magnitude than the incoming edge, its
preferred relation determines the player's strict best response. -/
theorem dominatedIncoming {k : ℕ} {flip : Fin k → Bool}
    (hflip : ∏ l, (if flip l then (-1 : ℝ) else 1) = -1)
    (payoff : (Fin k → Bool) → Fin k → ℝ) (outgoing incoming : Fin k → ℝ)
    (hdom : ∀ l, |incoming l| < outgoing l)
    (gain : ∀ (a : Fin k → Bool) l, a l ≠ (a (finRotate k l) ^^ flip l) →
      ∃ noise : ℝ, -|incoming l| ≤ noise ∧
        payoff (Function.update a l (!a l)) l - payoff a l = outgoing l + noise) :
    ¬ ∃ a, ∀ l b, payoff (Function.update a l b) l ≤ payoff a l := by
  apply no_binary_equilibrium hflip payoff
  intro a l hl
  obtain ⟨noise,hn,he⟩ := gain a l hl
  linarith [hdom l]

/-- Strict cyclic dominance can be scaled with real coefficients when the
product of the left gains exceeds the product of the right gains. -/
theorem strictScaling {k : ℕ} (hk : 0 < k)
    (left right : Fin k → ℝ) (hl : ∀ i, 0 < left i) (hr : ∀ i, 0 < right i)
    (hprod : (∏ i, right i) < ∏ i, left i) :
    ∃ scale : Fin k → ℝ, (∀ i, 0 < scale i) ∧
      ∀ i, scale i * right i < scale (finRotate k i) * left (finRotate k i) := by
  let r := fun i => right i / left (finRotate k i)
  have hrot : (∏ i, left (finRotate k i)) = ∏ i, left i :=
    Equiv.prod_comp (finRotate k) left
  have hp (i : Fin k) : 0 < r i := div_pos (hr i) (hl _)
  have hlt : (∏ i, r i) < 1 := by
    change (∏ i, right i / left (finRotate k i)) < 1
    rw [Finset.prod_div_distrib,hrot]
    exact (div_lt_one (Finset.prod_pos fun i _ => hl i)).2 hprod
  let c := (∏ i, r i) ^ (-(1 / (k : ℝ)))
  have hbase : 0 < ∏ i, r i := Finset.prod_pos fun i _ => hp i
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have hc : 1 < c := by
    dsimp [c]
    rw [Real.rpow_neg hbase.le, one_lt_inv₀]
    · exact Real.rpow_lt_one hbase.le hlt (one_div_pos.mpr hk')
    · exact Real.rpow_pos_of_pos hbase _
  have hclose : (∏ i, c * r i) = 1 := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    dsimp [c]
    rw [← Real.rpow_mul_natCast hbase.le]
    have he : -(1 / (k : ℝ)) * (k : ℝ) = -1 := by field_simp
    rw [he, Real.rpow_neg_one, inv_mul_cancel₀ hbase.ne']
  let scale := fun i : Fin k => ∏ j ∈ Finset.univ.filter (fun j : Fin k => j < i), c * r j
  have hs (i : Fin k) : 0 < scale i := Finset.prod_pos fun j _ => mul_pos (zero_lt_one.trans hc) (hp j)
  refine ⟨scale,hs,?_⟩
  intro i
  have he : scale (finRotate k i) = scale i * (c * r i) := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    by_cases hi : i = Fin.last m
    · subst i
      have hzero : finRotate (m+1) (Fin.last m) = 0 := by
        apply Fin.ext
        simp only [coe_finRotate, if_true, Fin.val_zero]
      rw [hzero]
      have hf : insert (Fin.last m) (Finset.univ.filter (fun j : Fin (m+1) => j < Fin.last m)) =
          Finset.univ := by
        ext j
        simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and,iff_true]
        exact (Fin.le_last j).eq_or_lt
      have hz : scale 0 = 1 := by simp [scale]
      rw [hz, ← hclose]
      conv_lhs => rw [← hf]
      rw [Finset.prod_insert (by simp),mul_comm]
    · have hf : Finset.univ.filter (fun j : Fin (m+1) => j < finRotate (m+1) i) =
          insert i (Finset.univ.filter (fun j : Fin (m+1) => j < i)) := by
        ext j
        simp only [Finset.mem_insert,Finset.mem_filter,Finset.mem_univ,true_and]
        change j.val < (finRotate (m+1) i).val ↔ _
        rw [coe_finRotate_of_ne_last hi]
        constructor
        · intro hh
          by_cases hji : j = i
          · exact Or.inl hji
          · exact Or.inr (Fin.lt_def.mpr (by
              have hv : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
              omega))
        · rintro (rfl | hh)
          · omega
          · have hv := Fin.lt_def.mp hh
            omega
      unfold scale
      rw [hf,Finset.prod_insert (by simp),mul_comm]
  rw [he]
  have hmul : r i * left (finRotate k i) = right i :=
    div_mul_cancel₀ _ (hl _).ne'
  have hh := mul_lt_mul_of_pos_left hc (mul_pos (hs i) (hr i))
  rw [mul_one] at hh
  calc
    _ < c * (scale i * right i)  := by simpa only [mul_comm c] using hh
    _ = _ := by rw [← hmul]; ring

end ShapleyBinaryCycle

namespace ShapleyBinaryCycle

/-- Zero incoming gains are allowed by perturbing them upward before choosing scales. -/
theorem strictScaling_nonneg {k : ℕ} (hk : 0 < k)
    (left right : Fin k → ℝ) (hl : ∀ i, 0 < left i) (hr : ∀ i, 0 ≤ right i)
    (hprod : (∏ i, right i) < ∏ i, left i) :
    ∃ scale : Fin k → ℝ, (∀ i, 0 < scale i) ∧
      ∀ i, scale i * right i < scale (finRotate k i) * left (finRotate k i) := by
  let F := fun t : ℝ => ∏ i : Fin k, (right i + t)
  have hc : Continuous F := by
    unfold F
    exact continuous_finsetProd _ fun i _ => continuous_const.add continuous_id
  have he : ∀ᶠ t in nhds (0 : ℝ), F t < ∏ i, left i :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa [F] using hprod)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp he
  have hhalf : 0 < δ / 2 := by positivity
  have hgood : F (δ / 2) < ∏ i, left i := by
    apply hball
    rw [Real.dist_eq,sub_zero,abs_of_pos hhalf]
    linarith
  obtain ⟨s,hs,hh⟩ := strictScaling hk left (fun i => right i + δ / 2) hl
    (fun i => add_pos_of_nonneg_of_pos (hr i) hhalf) hgood
  exact ⟨s,hs,fun i => (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right hhalf.le) (hs i).le).trans_lt (hh i)⟩

end ShapleyBinaryCycle

namespace ShapleyBinaryCycle

/-- Rounding after a common dilation preserves strict dominance. -/
theorem integerScaling {k : ℕ} (left right scale : Fin k → ℝ)
    (hl : ∀ i, 0 < left i) (hr : ∀ i, 0 ≤ right i) (hs : ∀ i, 0 < scale i)
    (hd : ∀ i, scale i * right i < scale (finRotate k i) * left (finRotate k i)) :
    ∃ copies : Fin k → ℕ, (∀ i, 0 < copies i) ∧
      ∀ i, (copies i : ℝ) * right i < (copies (finRotate k i) : ℝ) * left (finRotate k i) := by
  let gap := fun i => scale (finRotate k i) * left (finRotate k i) - scale i * right i
  have hg (i : Fin k) : 0 < gap i := sub_pos.mpr (hd i)
  let bound := fun i => (1 / scale i) + (left (finRotate k i) / gap i)
  have hb (i : Fin k) : 0 ≤ bound i :=
    add_nonneg (one_div_nonneg.mpr (hs i).le) (div_nonneg (hl _).le (hg i).le)
  obtain ⟨N,hN⟩ := exists_nat_gt (∑ i, bound i)
  let copies := fun i => ⌊(N : ℝ) * scale i⌋₊
  have hbound (i : Fin k) : bound i < N :=
    (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i)).trans_lt hN
  have hNpos : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  refine ⟨copies,?_,?_⟩
  · intro i
    have h1 : 1 / scale i < N := (le_add_of_nonneg_right
      (div_nonneg (hl _).le (hg i).le)).trans_lt (hbound i)
    have h2 := (div_lt_iff₀ (hs i)).mp h1
    exact Nat.pos_of_ne_zero fun hz => by
      have h := Nat.lt_floor_add_one ((N : ℝ) * scale i)
      change copies i = 0 at hz
      change (N : ℝ) * scale i < (copies i : ℝ) + 1 at h
      rw [hz,Nat.cast_zero,zero_add] at h
      exact (not_lt_of_ge h2.le) h
  · intro i
    let j := finRotate k i
    have h1 : left j / gap i < N :=
      (le_add_of_nonneg_left (one_div_nonneg.mpr (hs i).le)).trans_lt (hbound i)
    have h2 := (div_lt_iff₀ (hg i)).mp h1
    have hlow : (N : ℝ) * scale j - 1 < copies j := by
      have hh := Nat.lt_floor_add_one ((N : ℝ) * scale j)
      change (N : ℝ) * scale j < (copies j : ℝ) + 1 at hh
      linarith
    have hu : (copies i : ℝ) ≤ (N : ℝ) * scale i :=
      Nat.floor_le (mul_nonneg hNpos (hs i).le)
    calc
      _ ≤ ((N : ℝ) * scale i) * right i := mul_le_mul_of_nonneg_right hu (hr i)
      _ < ((N : ℝ) * scale j - 1) * left j := by
        dsimp [gap,j] at *
        nlinarith only [h2]
      _ < _ := mul_lt_mul_of_pos_right hlow (hl j)

end ShapleyBinaryCycle

namespace ShapleyBinaryCycle

theorem oneFlip {k : ℕ} (j : Fin k) :
    (∏ l, (if decide (l = j) then (-1 : ℝ) else 1)) = -1 := by
  rw [Finset.prod_eq_single j]
  · simp
  · intro l _ h
    simp [h]
  · simp

theorem orientedCopies {k : ℕ} (hk : 0 < k) (left right : Fin k → ℝ)
    (hl : ∀ i, 0 ≤ left i) (hr : ∀ i, 0 ≤ right i)
    (hprod : (∏ i, right i) < ∏ i, left i) :
    ∃ copies : Fin k → ℕ, (∀ i, 0 < copies i) ∧
      ∀ i, (copies i : ℝ) * right i < (copies (finRotate k i) : ℝ) * left (finRotate k i) := by
  have hp : ∀ i, 0 < left i := by
    intro i
    have hpositive := (Finset.prod_nonneg fun j (_ : j ∈ Finset.univ) => hr j).trans_lt hprod
    have hn : left i ≠ 0 := fun he => hpositive.ne' (Finset.prod_eq_zero (Finset.mem_univ i) he)
    exact lt_of_le_of_ne (hl i) hn.symm
  obtain ⟨s,hs,hd⟩ := strictScaling_nonneg hk left right hp hr hprod
  exact integerScaling left right s hp hr hs hd

end ShapleyBinaryCycle

open CostSharingPNE.Char CostSharingIndexedAux

namespace ShapleyCycleEdge

variable {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

noncomputable def leftPay (S : I → Finset (Fin n)) (z : I → ℤ)
    (W : I → Welfare n) (f : Welfare n → Rule n) (i j : Fin n) (a b : Bool) : ℝ :=
  ∑ r ∈ act (if a then botB S i else topB S i),
    Fsh S z W f i j (if b then rgtB S z j else lftB S z j) r

noncomputable def rightPay (S : I → Finset (Fin n)) (z : I → ℤ)
    (W : I → Welfare n) (f : Welfare n → Rule n) (i j : Fin n) (a b : Bool) : ℝ :=
  ∑ r ∈ act (if b then rgtB S z j else lftB S z j),
    Fsh S z W f j i (if a then botB S i else topB S i) r

theorem leftDifference (S : I → Finset (Fin n)) (z : I → ℤ)
    (W : I → Welfare n) (f : Welfare n → Rule n) (i j : Fin n)
    (h0 : ∀ V x T, x ∉ T → f V x T = 0) (b : Bool) :
    leftPay S z W f i j true b - leftPay S z W f i j false b =
      (if b then -1 else 1) *
        ∑ t, (z t : ℝ) * (f (W t) i (S t) - f (W t) i ((S t).erase j)) := by
  have ho (t : I) (ht : i ∉ S t) :
      f (W t) i (S t) = f (W t) i ((S t).erase j) :=
    (h0 _ _ _ ht).trans (h0 _ _ _ (fun h => ht (Finset.mem_of_mem_erase h))).symm
  cases b
  · simpa [leftPay] using Ki_lft S z i j W f ho
  · simpa [leftPay] using Ki_rgt S z i j W f ho

theorem rightDifference (S : I → Finset (Fin n)) (z : I → ℤ)
    (W : I → Welfare n) (f : Welfare n → Rule n) (i j : Fin n)
    (h0 : ∀ V x T, x ∉ T → f V x T = 0) (a : Bool) :
    rightPay S z W f i j a true - rightPay S z W f i j a false =
      (if a then -1 else 1) *
        ∑ t, (z t : ℝ) * (f (W t) j (S t) - f (W t) j ((S t).erase i)) := by
  have ho (t : I) (ht : j ∉ S t) :
      f (W t) j (S t) = f (W t) j ((S t).erase i) :=
    (h0 _ _ _ ht).trans (h0 _ _ _ (fun h => ht (Finset.mem_of_mem_erase h))).symm
  cases a
  · simpa [rightPay] using Kj_top S z i j W f ho
  · simpa [rightPay] using Kj_bot S z i j W f ho

end ShapleyCycleEdge

namespace ShapleyCycleEdge

theorem isolate {n : ℕ} (hn : 1 < n) (W : Welfare n) (f : Welfare n → Rule n)
    (hbb : IsBudgetBalanced (f W) W) (hp : GuaranteesPNE {W} f)
    (h0 : ∀ i S, i ∉ S → f W i S = 0) (T : Finset (Fin n)) (hT : T ∈ coalitions W)
    (i j : Fin n) (hi : i ∈ T) (hj : j ∈ T) (hne : i ≠ j) :
    ∃ z : {U // U ∈ coalitionsIn W T} → ℤ,
      (∑ u, (z u : ℝ) * (f W i u.1 - f W i (u.1.erase j))) =
        mobius W T * basisRule (f W) W T i T ∧
      (∑ u, (z u : ℝ) * (f W j u.1 - f W j (u.1.erase i))) =
        mobius W T * basisRule (f W) W T j T := by
  obtain ⟨c,hfull,herase⟩ := corollary_1 n hn W f hbb hp h0 T hT
  refine ⟨fun u => c u.1, ?_,?_⟩
  · rw [Finset.sum_coe_sort _ (fun u => (c u : ℝ) * (f W i u - f W i (u.erase j)))]
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [← hfull i hi, ← (herase i hi j hj hne.symm).2, ← (herase i hi j hj hne.symm).1,sub_zero]
  · rw [Finset.sum_coe_sort _ (fun u => (c u : ℝ) * (f W j u - f W j (u.erase i)))]
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [← hfull j hj, ← (herase j hj i hi hne).2, ← (herase j hj i hi hne).1,sub_zero]

end ShapleyCycleEdge

namespace ShapleyCycleEdge

variable {n : ℕ} {R : Type} [DecidableEq R] [Fintype R]

/-- A finite resource assignment with two strategic endpoints per resource.
All other players have membership fixed by the resource's coalition. -/
def uses (S : R → Finset (Fin n)) (left right : R → Fin n)
    (chooseLeft chooseRight : R → Bool → Bool)
    (a : Fin n → Bool) (i : Fin n) (r : R) : Prop :=
  i ∈ S r ∧ (if i = left r then chooseLeft r (a i) = true
    else if i = right r then chooseRight r (a i) = true else True)

instance usesDecidable (S : R → Finset (Fin n)) (left right : R → Fin n)
    (L B : R → Bool → Bool) (a : Fin n → Bool) (i : Fin n) (r : R) :
    Decidable (uses S left right L B a i r) := by
  unfold uses
  split <;> infer_instance

noncomputable def profile (S : R → Finset (Fin n)) (left right : R → Fin n)
    (chooseLeft chooseRight : R → Bool → Bool) (a : Fin n → Bool) :
    Fin n → Finset R := by
  classical
  exact fun i => Finset.univ.filter (uses S left right chooseLeft chooseRight a i)

@[simp] theorem mem_profile (S : R → Finset (Fin n)) (left right : R → Fin n)
    (chooseLeft chooseRight : R → Bool → Bool) (a : Fin n → Bool) (i : Fin n) (r : R) :
    r ∈ profile S left right chooseLeft chooseRight a i ↔
      uses S left right chooseLeft chooseRight a i r := by
  classical
  simp [profile]

theorem profile_update (S : R → Finset (Fin n)) (left right : R → Fin n)
    (chooseLeft chooseRight : R → Bool → Bool) (a : Fin n → Bool) (i : Fin n) (b : Bool) :
    profile S left right chooseLeft chooseRight (Function.update a i b) =
      Function.update (profile S left right chooseLeft chooseRight a) i
        (profile S left right chooseLeft chooseRight (fun _ => b) i) := by
  classical
  funext j
  ext r
  by_cases h : j = i
  · subst j
    simp [uses]
  · simp [Function.update_of_ne h, uses]

theorem nonincident_payoff (S : R → Finset (Fin n)) (left right : R → Fin n)
    (chooseLeft chooseRight : R → Bool → Bool) (a : Fin n → Bool) (i : Fin n) (b : Bool)
    (r : R) (hl : i ≠ left r) (hr : i ≠ right r) :
    pl (profile S left right chooseLeft chooseRight (Function.update a i b)) r =
      pl (profile S left right chooseLeft chooseRight a) r := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp [pl, uses, hl, hr]
  · simp [pl, uses, Function.update_of_ne hj]

end ShapleyCycleEdge

namespace ShapleyCycleEdge

variable {n : ℕ} {R : Type} [DecidableEq R] [Fintype R]

noncomputable def binaryPayoff (S : R → Finset (Fin n)) (left right : R → Fin n)
    (chooseLeft chooseRight : R → Bool → Bool) (W : R → Welfare n)
    (f : Welfare n → Rule n) (copies : R → ℕ) (a : Fin n → Bool) (i : Fin n) : ℝ :=
  ∑ r ∈ profile S left right chooseLeft chooseRight a i,
    (copies r : ℝ) * f (W r) i (pl (profile S left right chooseLeft chooseRight a) r)

theorem binaryEquilibrium (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hp : GuaranteesPNE V f) (hV : V.Nonempty)
    (S : R → Finset (Fin n)) (left right : R → Fin n)
    (chooseLeft chooseRight : R → Bool → Bool) (W : R → Welfare n)
    (hW : ∀ r, W r ∈ V) (copies : R → ℕ) :
    ∃ a : Fin n → Bool, ∀ i b,
      binaryPayoff S left right chooseLeft chooseRight W f copies (Function.update a i b) i ≤
      binaryPayoff S left right chooseLeft chooseRight W f copies a i := by
  classical
  let action := fun (i : Fin n) (b : Bool) =>
    profile S left right chooseLeft chooseRight (fun _ => b) i
  let A := fun i => ({action i false, action i true} : Finset (Finset R))
  obtain ⟨V₀,hV₀⟩ := hV
  obtain ⟨x,hx,hbest⟩ := weighted_pne V f hp V₀ hV₀ W hW copies A (fun i => by simp [A])
  have hchoice (i : Fin n) : ∃ b, x i = action i b := by
    have he := hx i
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at he
    exact he.elim (fun h => ⟨false,h⟩) (fun h => ⟨true,h⟩)
  choose a ha using hchoice
  have hprof : profile S left right chooseLeft chooseRight a = x := by
    funext i
    rw [ha i]
    ext r
    simp [action,uses]
  refine ⟨a,?_⟩
  intro i b
  unfold binaryPayoff
  rw [profile_update,hprof,Function.update_self]
  exact hbest i (action i b) (by cases b <;> simp [A])

end ShapleyCycleEdge

namespace ShapleyCycleEdge

variable {n : ℕ} {R : Type} [DecidableEq R] [Fintype R]

theorem participantSet (S : R → Finset (Fin n)) (left right : R → Fin n)
    (L B : R → Bool → Bool) (a : Fin n → Bool) (r : R) (hne : left r ≠ right r) :
    pl (profile S left right L B a) r =
      ((if L r (a (left r)) then S r else (S r).erase (left r))).filter
        (fun j => j ≠ right r ∨ B r (a (right r)) = true) := by
  classical
  ext j
  by_cases hl : j = left r
  · subst j
    cases h : L r (a (left r)) <;> simp [pl,uses,h,hne]
  · by_cases hr : j = right r
    · subst j
      cases h : L r (a (left r)) <;> simp [pl,uses,h,hne.symm]
    · cases h : L r (a (left r)) <;> simp [pl,uses,h,hl,hr]

theorem payoff_eq_sum (S : R → Finset (Fin n)) (left right : R → Fin n)
    (L B : R → Bool → Bool) (W : R → Welfare n) (f : Welfare n → Rule n)
    (copies : R → ℕ) (a : Fin n → Bool) (i : Fin n) :
    binaryPayoff S left right L B W f copies a i =
      ∑ r, if uses S left right L B a i r
        then (copies r : ℝ) * f (W r) i (pl (profile S left right L B a) r) else 0 := by
  classical
  unfold binaryPayoff profile
  rw [Finset.sum_filter]

end ShapleyCycleEdge

namespace ShapleyCycleEdge

variable {n : ℕ} {R : Type} [DecidableEq R] [Fintype R]

/-- Only resources where the deviator is a strategic endpoint contribute to
the gain, even if the deviator belongs to other resource coalitions. -/
theorem deviation_eq_incident_sum (S : R → Finset (Fin n)) (left right : R → Fin n)
    (L B : R → Bool → Bool) (W : R → Welfare n) (f : Welfare n → Rule n)
    (copies : R → ℕ) (a : Fin n → Bool) (i : Fin n) (b : Bool) :
    binaryPayoff S left right L B W f copies (Function.update a i b) i -
      binaryPayoff S left right L B W f copies a i =
    ∑ r ∈ Finset.univ.filter (fun r => i = left r ∨ i = right r),
      ((if uses S left right L B (Function.update a i b) i r then
        (copies r : ℝ) * f (W r) i (pl (profile S left right L B (Function.update a i b)) r)
        else 0) -
      (if uses S left right L B a i r then
        (copies r : ℝ) * f (W r) i (pl (profile S left right L B a) r) else 0)) := by
  classical
  rw [payoff_eq_sum, payoff_eq_sum, ← Finset.sum_sub_distrib]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro r _ hr
  have hne : ¬ (i = left r ∨ i = right r) := by simpa using hr
  have hl : i ≠ left r := fun h => hne (Or.inl h)
  have hh : i ≠ right r := fun h => hne (Or.inr h)
  rw [nonincident_payoff S left right L B a i b r hl hh]
  simp only [uses, if_neg hl, if_neg hh, and_true, sub_self]

end ShapleyCycleEdge

namespace ShapleyCycleEdge

variable {n : ℕ} {I : Type} [Fintype I] [DecidableEq I]

def leftChoice (r : Res I) (b : Bool) : Bool := decide (r.2 = if b then 1 else 0)

def rightChoice (z : I → ℤ) (r : Res I) (b : Bool) : Bool :=
  decide (if b then (r.2 = 0 ∧ 0 < z r.1) ∨ (r.2 = 1 ∧ z r.1 < 0)
    else (r.2 = 0 ∧ z r.1 < 0) ∨ (r.2 = 1 ∧ 0 < z r.1))

theorem endpointPayoffs (S : I → Finset (Fin n)) (z : I → ℤ)
    (W : I → Welfare n) (f : Welfare n → Rule n) (i j : Fin n) (hne : i ≠ j)
    (a : Fin n → Bool) :
    binaryPayoff (fun r : Res I => S r.1) (fun _ => i) (fun _ => j)
      leftChoice (rightChoice z) (fun r => W r.1) f (vw z) a i =
        leftPay S z W f i j (a i) (a j) ∧
    binaryPayoff (fun r : Res I => S r.1) (fun _ => i) (fun _ => j)
      leftChoice (rightChoice z) (fun r => W r.1) f (vw z) a j =
        rightPay S z W f i j (a i) (a j) := by
  classical
  let P := profile (fun r : Res I => S r.1) (fun _ => i) (fun _ => j) leftChoice (rightChoice z) a
  let L := if a i then botB S i else topB S i
  let B := if a j then rgtB S z j else lftB S z j
  have hL (r : Res I) : r ∈ P i ↔ r ∈ act L := by
    change r ∈ profile _ _ _ _ _ _ i ↔ _
    rw [mem_profile,mem_act]
    cases ha : a i <;> simp [uses,leftChoice,L,ha,botB,topB,and_comm]
  have hB (r : Res I) : r ∈ P j ↔ r ∈ act B := by
    change r ∈ profile _ _ _ _ _ _ j ↔ _
    rw [mem_profile,mem_act]
    cases ha : a j <;> simp [uses,rightChoice,B,ha,rgtB,lftB,hne.symm]
  have hCoal (r : Res I) (x y : Fin n) (hxy : x ≠ y)
      (h : ∀ u, u = x ∨ u = y → u = i ∨ u = j)
      (hx : r ∈ P x) :
      pl P r = if r ∈ P y then S r.1 else (S r.1).erase y := by
    have hm (u : Fin n) : r ∈ P u → u ∈ S r.1 :=
      fun hu => ((mem_profile _ _ _ _ _ _ _ _).mp hu).1
    have hfixed (u : Fin n) (hu : u ≠ x) (hv : u ≠ y) :
        r ∈ P u ↔ u ∈ S r.1 := by
      have hkeys : x = i ∧ y = j ∨ x = j ∧ y = i := by
        rcases h x (Or.inl rfl) with hi | hj
        · rcases h y (Or.inr rfl) with hy | hy
          · exact False.elim (hxy (hi.trans hy.symm))
          · exact Or.inl ⟨hi,hy⟩
        · rcases h y (Or.inr rfl) with hy | hy
          · exact Or.inr ⟨hj,hy⟩
          · exact False.elim (hxy (hj.trans hy.symm))
      have hi : u ≠ i := by rcases hkeys with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
      have hj : u ≠ j := by rcases hkeys with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> assumption
      exact mem_profile _ _ _ _ _ _ _ _ |>.trans (by simp [uses,hi,hj])
    ext u
    simp only [pl,Finset.mem_filter,Finset.mem_univ,true_and]
    by_cases hy : r ∈ P y
    · rw [if_pos hy]
      by_cases hux : u = x
      · subst u; simp [hx,hm _ hx]
      · by_cases huy : u = y
        · subst u; simp [hy,hm _ hy]
        · exact hfixed _ hux huy
    · rw [if_neg hy,Finset.mem_erase]
      by_cases hux : u = x
      · subst u; simp [hx,hm _ hx,hxy]
      · by_cases huy : u = y
        · subst u; simp [hy]
        · rw [hfixed _ hux huy]; simp [huy]
  constructor
  · change (∑ r ∈ P i, _) = ∑ r ∈ act L, Fsh S z W f i j B r
    rw [show P i = act L from Finset.ext hL]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hCoal r i j hne (fun _ h => h) ((hL r).2 hr)]
    simp only [Fsh,hB,mem_act]
  · change (∑ r ∈ P j, _) = ∑ r ∈ act B, Fsh S z W f j i L r
    rw [show P j = act B from Finset.ext hB]
    apply Finset.sum_congr rfl
    intro r hr
    rw [hCoal r j i hne.symm (fun _ h => h.elim Or.inr Or.inl) ((hB r).2 hr)]
    simp only [Fsh,hL,mem_act]

end ShapleyCycleEdge

namespace ShapleyBinaryCycle

private lemma edge_gain {a b : Bool} {P : Bool → ℝ} {g : ℝ}
    (h : P true - P false = (if b then -1 else 1) * g) :
    P (!a) - P a = (if a == b then 1 else -1) * g := by
  cases a <;> cases b <;> simp_all <;> linarith

/-- Each player's utility has one outgoing term, one incoming term, and
terms independent of that player's action. -/
theorem no_equilibrium_of_edge_payoffs {k : ℕ} {flip : Fin k → Bool}
    (hflip : ∏ l, (if flip l then (-1 : ℝ) else 1) = -1)
    (L R : Fin k → Bool → Bool → ℝ) (leftGain rightGain : Fin k → ℝ)
    (hL : ∀ l b, L l true b - L l false b =
      (if b then -1 else 1) * leftGain l)
    (hR : ∀ l b, R l b true - R l b false =
      (if b then -1 else 1) * rightGain l)
    (hsign : ∀ l, (if flip l then 1 else -1) * leftGain l = |leftGain l|)
    (hdom : ∀ l, |rightGain ((finRotate k).symm l)| < |leftGain l|)
    (payoff : (Fin k → Bool) → Fin k → ℝ)
    (hdecomp : ∀ a l, let p := (finRotate k).symm l
      payoff (Function.update a l (!a l)) l - payoff a l =
        (L l (!a l) (a (finRotate k l)) - L l (a l) (a (finRotate k l))) +
        (R p (a p) (!a l) - R p (a p) (a l))) :
    ¬ ∃ a, ∀ l b, payoff (Function.update a l b) l ≤ payoff a l := by
  apply dominatedIncoming hflip payoff (fun l => |leftGain l|)
    (fun l => rightGain ((finRotate k).symm l)) hdom
  intro a l hl
  let p := (finRotate k).symm l
  have hleft : L l (!a l) (a (finRotate k l)) - L l (a l) (a (finRotate k l)) =
      |leftGain l| := by
    rw [edge_gain (P := fun b => L l b (a (finRotate k l))) (a := a l) (hL l (a (finRotate k l)))]
    rw [← hsign l]
    have hc : (if a l == a (finRotate k l) then (1 : ℝ) else -1) =
        if flip l then 1 else -1 := by
      revert hl
      cases a l <;> cases a (finRotate k l) <;> cases flip l <;> simp
    rw [hc]
  let noise := R p (a p) (!a l) - R p (a p) (a l)
  refine ⟨noise,?_,?_⟩
  · change -|rightGain p| ≤ R p (a p) (!a l) - R p (a p) (a l)
    rw [edge_gain (P := R p (a p)) (a := a l) (hR p (a p))]
    split
    · simpa using (neg_abs_le (rightGain p))
    · simpa using (neg_le_neg (le_abs_self (rightGain p)))
  · rw [hdecomp,hleft]

end ShapleyBinaryCycle

open CostSharingPNE.Char CostSharingIndexedAux ShapleyCycleEdge

namespace ShapleyCycleGame

variable {n k : ℕ} {I : Fin k → Type} [∀ l, Fintype (I l)] [∀ l, DecidableEq (I l)]

abbrev Resource (I : Fin k → Type) := Σ l, Res (I l)

noncomputable def localPay (S : ∀ l, I l → Finset (Fin n)) (z : ∀ l, I l → ℤ)
    (W : ∀ l, I l → Welfare n) (f : Welfare n → Rule n) (p : Fin k → Fin n)
    (a : Fin n → Bool) (i : Fin n) (l : Fin k) : ℝ :=
  binaryPayoff (fun r : Res (I l) => S l r.1) (fun _ => p l)
    (fun _ => p (finRotate k l)) leftChoice (rightChoice (z l))
    (fun r => W l r.1) f (vw (z l)) a i

noncomputable def totalPay (S : ∀ l, I l → Finset (Fin n)) (z : ∀ l, I l → ℤ)
    (W : ∀ l, I l → Welfare n) (f : Welfare n → Rule n) (p : Fin k → Fin n)
    (a : Fin n → Bool) (i : Fin n) : ℝ :=
  ∑ l, localPay S z W f p a i l

theorem totalEquilibrium (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hp : GuaranteesPNE V f) (hV : V.Nonempty)
    (S : ∀ l, I l → Finset (Fin n)) (z : ∀ l, I l → ℤ)
    (W : ∀ l, I l → Welfare n) (hW : ∀ l t, W l t ∈ V)
    (p : Fin k → Fin n) :
    ∃ a : Fin n → Bool, ∀ i b,
      totalPay S z W f p (Function.update a i b) i ≤ totalPay S z W f p a i := by
  classical
  let coal := fun r : Resource I => S r.1 r.2.1
  let left := fun r : Resource I => p r.1
  let right := fun r : Resource I => p (finRotate k r.1)
  let L := fun (r : Resource I) b => leftChoice r.2 b
  let B := fun (r : Resource I) b => rightChoice (z r.1) r.2 b
  let welfare := fun r : Resource I => W r.1 r.2.1
  let copies := fun r : Resource I => vw (z r.1) r.2
  have he (a : Fin n → Bool) (i : Fin n) :
      binaryPayoff coal left right L B welfare f copies a i = totalPay S z W f p a i := by
    rw [payoff_eq_sum,Fintype.sum_sigma]
    unfold totalPay localPay
    apply Finset.sum_congr rfl
    intro l _
    rw [payoff_eq_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hpl : pl (profile coal left right L B a) ⟨l,r⟩ =
        pl (profile (fun r : Res (I l) => S l r.1) (fun _ => p l)
          (fun _ => p (finRotate k l)) leftChoice (rightChoice (z l)) a) r := by
      ext j
      simp only [pl,Finset.mem_filter,Finset.mem_univ,true_and,mem_profile]
      rfl
    simp only [hpl]
    rfl
  obtain ⟨a,ha⟩ := binaryEquilibrium V f hp hV coal left right L B welfare (fun r => hW r.1 r.2.1) copies
  exact ⟨a,fun i b => by simpa only [he] using ha i b⟩

theorem localDeviationZero (S : ∀ l, I l → Finset (Fin n)) (z : ∀ l, I l → ℤ)
    (W : ∀ l, I l → Welfare n) (f : Welfare n → Rule n) (p : Fin k → Fin n)
    (a : Fin n → Bool) (i : Fin n) (l : Fin k) (b : Bool)
    (hl : i ≠ p l) (hr : i ≠ p (finRotate k l)) :
    localPay S z W f p (Function.update a i b) i l - localPay S z W f p a i l = 0 := by
  unfold localPay
  rw [deviation_eq_incident_sum]
  simp only [hl,hr,or_self,Finset.filter_false,Finset.sum_empty]

end ShapleyCycleGame

namespace ShapleyCycleGame
variable {n k : ℕ} {I : Fin k → Type} [∀ l, Fintype (I l)] [∀ l, DecidableEq (I l)]

theorem totalDeviation (S : ∀ l, I l → Finset (Fin n)) (z : ∀ l, I l → ℤ)
    (W : ∀ l, I l → Welfare n) (f : Welfare n → Rule n) (p : Fin k → Fin n)
    (pinj : Function.Injective p) (hne : ∀ l, l ≠ finRotate k l)
    (a : Fin n → Bool) (l : Fin k) (b : Bool) :
    let q := (finRotate k).symm l
    totalPay S z W f p (Function.update a (p l) b) (p l) - totalPay S z W f p a (p l) =
      (leftPay (S l) (z l) (W l) f (p l) (p (finRotate k l)) b (a (p (finRotate k l))) -
        leftPay (S l) (z l) (W l) f (p l) (p (finRotate k l)) (a (p l)) (a (p (finRotate k l)))) +
      (rightPay (S q) (z q) (W q) f (p q) (p l) (a (p q)) b -
        rightPay (S q) (z q) (W q) f (p q) (p l) (a (p q)) (a (p l))) := by
  classical
  dsimp only
  let q := (finRotate k).symm l
  have hq : finRotate k q = l := (finRotate k).apply_symm_apply l
  have hql : q ≠ l := fun h => hne l (by simpa [h] using hq.symm)
  let d := fun j => localPay S z W f p (Function.update a (p l) b) (p l) j -
    localPay S z W f p a (p l) j
  have hz : ∀ j, j ∉ ({l,q} : Finset (Fin k)) → d j = 0 := by
    intro j hj
    apply localDeviationZero
    · intro he
      exact hj (by simp [pinj he])
    · intro he
      have hh : j = q := (finRotate k).injective ((pinj he).symm.trans hq.symm)
      exact hj (by simp [hh])
  have hsum : (∑ j, d j) = d l + d q := by
    rw [← Finset.sum_subset (Finset.subset_univ ({l,q} : Finset (Fin k))) (fun j _ hj => hz j hj)]
    simp [Ne.symm hql]
  unfold totalPay
  rw [← Finset.sum_sub_distrib]
  change (∑ j, d j) = _
  rw [hsum]
  have hl (v : Fin n → Bool) := (endpointPayoffs (S l) (z l) (W l) f _ _
    (fun hh => hne l (pinj hh)) v).1
  have hr (v : Fin n → Bool) :
      localPay S z W f p v (p l) q =
        rightPay (S q) (z q) (W q) f (p q) (p l) (v (p q)) (v (p l)) := by
    have he := (endpointPayoffs (S q) (z q) (W q) f (p q) (p (finRotate k q))
      (fun hh => hne q (pinj hh)) v).2
    unfold localPay
    simpa only [hq] using he
  have hl' (v : Fin n → Bool) : localPay S z W f p v (p l) l =
    leftPay (S l) (z l) (W l) f (p l) (p (finRotate k l)) (v (p l)) (v (p (finRotate k l))) :=
    hl v
  simp only [d,hl',hr,Function.update_self,
    Function.update_of_ne (fun h => hne l (pinj h).symm),
    Function.update_of_ne (fun h => hql (pinj h))]
  rfl

end ShapleyCycleGame

namespace ShapleyCycleGame

variable {n k : ℕ} {I : Fin k → Type} [∀ l, Fintype (I l)] [∀ l, DecidableEq (I l)]

theorem cycleImpossible (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hp : GuaranteesPNE V f) (hV : V.Nonempty)
    (h0 : ∀ W i T, i ∉ T → f W i T = 0)
    (S : ∀ l, I l → Finset (Fin n)) (z : ∀ l, I l → ℤ)
    (W : ∀ l, I l → Welfare n) (hW : ∀ l t, W l t ∈ V)
    (p : Fin k → Fin n) (pinj : Function.Injective p) (hne : ∀ l, l ≠ finRotate k l)
    (flip : Fin k → Bool) (hflip : ∏ l, (if flip l then (-1 : ℝ) else 1) = -1)
    (leftGain rightGain : Fin k → ℝ)
    (hl : ∀ l, (∑ t, (z l t : ℝ) * (f (W l t) (p l) (S l t) -
      f (W l t) (p l) ((S l t).erase (p (finRotate k l))))) = leftGain l)
    (hr : ∀ l, (∑ t, (z l t : ℝ) * (f (W l t) (p (finRotate k l)) (S l t) -
      f (W l t) (p (finRotate k l)) ((S l t).erase (p l)))) = rightGain l)
    (hsign : ∀ l, (if flip l then 1 else -1) * leftGain l = |leftGain l|)
    (hdom : ∀ l, |rightGain ((finRotate k).symm l)| < |leftGain l|) : False := by
  classical
  let L l := leftPay (S l) (z l) (W l) f (p l) (p (finRotate k l))
  let B l := rightPay (S l) (z l) (W l) f (p l) (p (finRotate k l))
  let extend (a : Fin k → Bool) (i : Fin n) :=
    if h : ∃ l, p l = i then a (Classical.choose h) else false
  have hex (a : Fin k → Bool) (l : Fin k) : extend a (p l) = a l := by
    have h : ∃ j, p j = p l := ⟨l,rfl⟩
    exact (dif_pos h).trans (congrArg a (pinj (Classical.choose_spec h)))
  have hupdate (a : Fin k → Bool) (l : Fin k) (b : Bool) :
      extend (Function.update a l b) = Function.update (extend a) (p l) b := by
    funext i
    by_cases h : ∃ j, p j = i
    · obtain ⟨j,rfl⟩ := h
      rw [hex,Function.update_apply]
      by_cases hj : j = l
      · subst j; simp
      · simp [hj,Function.update_of_ne (fun e => hj (pinj e)),hex]
    · have hi : i ≠ p l := fun e => h ⟨l,e.symm⟩
      simp [extend,h,Function.update_of_ne hi]
  let pay := fun a l => totalPay S z W f p (extend a) (p l)
  have hnone := ShapleyBinaryCycle.no_equilibrium_of_edge_payoffs hflip L B leftGain rightGain
    (fun l b => by simpa only [L,hl l] using leftDifference (S l) (z l) (W l) f (p l) (p (finRotate k l)) h0 b)
    (fun l b => by simpa only [B,hr l] using rightDifference (S l) (z l) (W l) f (p l) (p (finRotate k l)) h0 b)
    hsign hdom pay (fun a l => by
      simp only [pay,hupdate]
      have he := totalDeviation S z W f p pinj hne (extend a) l (!a l)
      have hq : finRotate k ((finRotate k).symm l) = l := (finRotate k).apply_symm_apply l
      simpa only [L,B,hq,hex] using he)
  obtain ⟨a,ha⟩ := totalEquilibrium V f hp hV S z W hW p
  let small := a ∘ p
  -- The choices of players outside the cycle have no effect on any resource.
  have hprofiles (b c : Fin n → Bool) (h : ∀ l, b (p l) = c (p l)) (l : Fin k) :
      profile (fun r : Res (I l) => S l r.1) (fun _ => p l) (fun _ => p (finRotate k l))
        leftChoice (rightChoice (z l)) b =
      profile (fun r : Res (I l) => S l r.1) (fun _ => p l) (fun _ => p (finRotate k l))
        leftChoice (rightChoice (z l)) c := by
    funext j
    ext r
    simp only [mem_profile,uses]
    split
    · rename_i hj
      subst j
      rw [h l]
    · split
      · rename_i hj
        subst j
        rw [h (finRotate k l)]
      · rfl
  have hpayeq (b c : Fin n → Bool) (h : ∀ l, b (p l) = c (p l)) (i : Fin n) :
      totalPay S z W f p b i = totalPay S z W f p c i := by
    unfold totalPay
    apply Finset.sum_congr rfl
    intro l _
    unfold localPay binaryPayoff
    rw [hprofiles b c h l]
  apply hnone
  refine ⟨small,?_⟩
  intro l b
  change totalPay S z W f p (extend (Function.update small l b)) (p l) ≤
    totalPay S z W f p (extend small) (p l)
  rw [hupdate, hpayeq _ a (fun j => hex small j)]
  rw [hpayeq _ (Function.update a (p l) b) (fun j => by
    by_cases h : p j = p l
    · simp [h]
    · simp only [Function.update_of_ne h,hex]; rfl)]
  exact ha (p l) b

end ShapleyCycleGame

namespace ShapleyCycleGame

theorem scaledCycleImpossible {n k : ℕ} {I : Fin k → Type}
    [∀ l, Fintype (I l)] [∀ l, DecidableEq (I l)]
    (hk : 0 < k) (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hp : GuaranteesPNE V f) (hV : V.Nonempty) (h0 : ∀ W i T, i ∉ T → f W i T = 0)
    (S : ∀ l, I l → Finset (Fin n)) (z : ∀ l, I l → ℤ)
    (W : ∀ l, I l → Welfare n) (hW : ∀ l t, W l t ∈ V)
    (p : Fin k → Fin n) (pinj : Function.Injective p) (hne : ∀ l, l ≠ finRotate k l)
    (left right : Fin k → ℝ)
    (hl : ∀ l, (∑ t, (z l t : ℝ) * (f (W l t) (p l) (S l t) -
      f (W l t) (p l) ((S l t).erase (p (finRotate k l))))) = left l)
    (hr : ∀ l, (∑ t, (z l t : ℝ) * (f (W l t) (p (finRotate k l)) (S l t) -
      f (W l t) (p (finRotate k l)) ((S l t).erase (p l)))) = right l)
    (hprod : (∏ l, |right l|) < ∏ l, |left l|) : False := by
  classical
  obtain ⟨copies,hcopies,hdom⟩ := ShapleyBinaryCycle.orientedCopies hk
    (fun l => |left l|) (fun l => |right l|) (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) hprod
  let j : Fin k := ⟨0,hk⟩
  let flip := fun l : Fin k => decide (l = j)
  let sign := fun l : Fin k => if (flip l = true) = (0 ≤ left l) then (1 : ℤ) else -1
  let c := fun l : Fin k => (copies l : ℤ) * sign l
  have hsign (l : Fin k) : (if flip l then 1 else -1) * ((c l : ℝ) * left l) =
      (copies l : ℝ) * |left l| := by
    by_cases h : flip l = true <;> by_cases h' : 0 ≤ left l <;>
      simp [c,sign,h,h',abs_of_nonneg,abs_of_nonpos,le_of_not_ge,mul_assoc]
  have hcabs (l : Fin k) : |(c l : ℝ)| = copies l := by
    by_cases h : (flip l = true) ↔ (0 ≤ left l) <;> simp [c,sign,h,abs_of_nonneg]
  have had (l : Fin k) : |(c l : ℝ) * left l| = (copies l : ℝ) * |left l| := by
    rw [abs_mul,hcabs]
  apply cycleImpossible V f hp hV h0 S (fun l t => c l * z l t) W hW p pinj hne flip
    (ShapleyBinaryCycle.oneFlip j) (fun l => (c l : ℝ) * left l) (fun l => (c l : ℝ) * right l)
  · intro l
    simp only [Int.cast_mul,mul_assoc,← Finset.mul_sum,hl l]
  · intro l
    simp only [Int.cast_mul,mul_assoc,← Finset.mul_sum,hr l]
  · intro l
    exact (hsign l).trans (had l).symm
  · intro l
    rw [abs_mul,hcabs,had]
    have he := hdom ((finRotate k).symm l)
    simpa only [Equiv.apply_symm_apply] using he

end ShapleyCycleGame

open CostSharingPNE.Char ShapleyCycleGame

namespace ShapleyCycleGame

theorem forwardProductBound {n k : ℕ} (hn : 1 < n) (hk : 0 < k)
    (W : Fin k → Welfare n) (f : Welfare n → Rule n)
    (hbb : ∀ l, IsBudgetBalanced (f (W l)) (W l))
    (h0 : ∀ V i S, i ∉ S → f V i S = 0)
    (hp : GuaranteesPNE (Set.range W) f)
    (p : Fin k → Fin n) (pinj : Function.Injective p) (hne : ∀ l, l ≠ finRotate k l)
    (T : Fin k → Finset (Fin n))
    (hT : ∀ l, T l ∈ coalitionsPair (W l) (p l) (p (finRotate k l))) :
    (∏ l, |basisRule (f (W l)) (W l) (T l) (p l) (T l)|) ≤
      ∏ l, |basisRule (f (W l)) (W l) (T l) (p (finRotate k l)) (T l)| := by
  classical
  by_contra! hlt
  have hi (l : Fin k) := Finset.mem_filter.mp (hT l)
  have hsingle (l : Fin k) : GuaranteesPNE {W l} f := by
    apply CostSharingIndexedAux.guarantees_mono f _ hp
    intro v hv
    exact ⟨l,(Set.mem_singleton_iff.mp hv).symm⟩
  choose z hz using fun l => ShapleyCycleEdge.isolate hn (W l) f (hbb l)
    (hsingle l) (h0 _) (T l) (hi l).1 (p l) (p (finRotate k l))
      (hi l).2.1 (hi l).2.2 (fun he => hne l (pinj he))
  let left l := mobius (W l) (T l) * basisRule (f (W l)) (W l) (T l) (p l) (T l)
  let right l := mobius (W l) (T l) * basisRule (f (W l)) (W l) (T l) (p (finRotate k l)) (T l)
  have hprod : (∏ l, |right l|) < ∏ l, |left l| := by
    simp only [right,left,abs_mul,Finset.prod_mul_distrib]
    apply mul_lt_mul_of_pos_left hlt
    apply Finset.prod_pos
    intro l _
    exact abs_pos.mpr (Finset.mem_filter.mp (hi l).1).2.2
  exact scaledCycleImpossible hk (Set.range W) f hp ⟨W ⟨0,hk⟩,⟨⟨0,hk⟩,rfl⟩⟩ h0
    (fun _ t => t.1) z (fun l _ => W l) (fun l _ => ⟨l,rfl⟩) p pinj hne left right
      (fun l => (hz l).1) (fun l => (hz l).2) hprod

end ShapleyCycleGame

namespace ShapleyCycleGame

theorem distinctCycleProducts {n k : ℕ} (hn : 1 < n) (hk : 3 ≤ k)
    (W : Fin k → Welfare n) (f : Welfare n → Rule n)
    (hbb : ∀ l, IsBudgetBalanced (f (W l)) (W l))
    (h0 : ∀ V i S, i ∉ S → f V i S = 0)
    (hp : GuaranteesPNE (Set.range W) f)
    (p : Fin k → Fin n) (pinj : Function.Injective p)
    (T : Fin k → Finset (Fin n))
    (hT : ∀ l, T l ∈ coalitionsPair (W l) (p l) (p (finRotate k l))) :
    (∏ l, |basisRule (f (W l)) (W l) (T l) (p l) (T l)|) =
      ∏ l, |basisRule (f (W l)) (W l) (T l) (p (finRotate k l)) (T l)| := by
  haveI : NeZero k := ⟨by omega⟩
  have hne (l : Fin k) : l ≠ finRotate k l := by
    intro he
    rw [finRotate_apply] at he
    have h := add_left_cancel (show l + 0 = l + 1 by simpa using he)
    have hv := congrArg Fin.val h
    simp [Fin.val_one, Nat.mod_eq_of_lt (show 1 < k by omega)] at hv
  apply le_antisymm (forwardProductBound hn (by omega) W f hbb h0 hp p pinj hne T hT)
  let rev : Fin k ≃ Fin k := ⟨Neg.neg,Neg.neg,neg_neg,neg_neg⟩
  let edge := rev.trans (finRotate k).symm
  have hrev (l : Fin k) : rev (finRotate k l) = edge l := by
    change -(finRotate k l) = (finRotate k).symm (-l)
    rw [finRotate_apply,finRotate_symm_apply,neg_add_rev]
    abel
  have hfirst (l : Fin k) : finRotate k (edge l) = rev l :=
    (finRotate k).apply_symm_apply (rev l)
  have hnew (l : Fin k) : T (edge l) ∈
      coalitionsPair (W (edge l)) (p (rev l)) (p (rev (finRotate k l))) := by
    have h := Finset.mem_filter.mp (hT (edge l))
    rw [hrev]
    exact Finset.mem_filter.mpr ⟨h.1,hfirst l ▸ h.2.2,h.2.1⟩
  have hrange : Set.range (W ∘ edge) = Set.range W := edge.surjective.range_comp W
  have hle := forwardProductBound hn (by omega) (W ∘ edge) f
    (fun l => hbb (edge l)) h0 (hrange.symm ▸ hp) (p ∘ rev)
    (pinj.comp rev.injective) hne (T ∘ edge) hnew
  change (∏ l, |basisRule (f (W (edge l))) (W (edge l)) (T (edge l)) (p (rev l)) (T (edge l))|) ≤
    ∏ l, |basisRule (f (W (edge l))) (W (edge l)) (T (edge l))
      (p (rev (finRotate k l))) (T (edge l))| at hle
  simp_rw [hrev] at hle
  conv at hle => lhs; enter [2,l]; rw [← hfirst l]
  rw [show (∏ l, |basisRule (f (W (edge l))) (W (edge l)) (T (edge l))
      (p (finRotate k (edge l))) (T (edge l))|) = _ from
      Equiv.prod_comp edge (fun l => |basisRule (f (W l)) (W l) (T l)
        (p (finRotate k l)) (T l)|),
    show (∏ l, |basisRule (f (W (edge l))) (W (edge l)) (T (edge l))
      (p (edge l)) (T (edge l))|) = _ from
      Equiv.prod_comp edge (fun l => |basisRule (f (W l)) (W l) (T l)
        (p l) (T l)|)] at hle
  exact hle

end ShapleyCycleGame

open CostSharingPNE.Char

namespace ShapleyCycleGame

theorem basisNonneg {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n) (hp : GuaranteesPNE V f)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W) (h0 : ∀ W i S, i ∉ S → f W i S = 0)
    {W : Welfare n} (hW : W ∈ V) {T : Finset (Fin n)} (hT : T ∈ coalitions W)
    (i : Fin n) (S : Finset (Fin n)) : 0 ≤ basisRule (f W) W T i S := by
  have hs : GuaranteesPNE {W} f :=
    CostSharingIndexedAux.guarantees_mono f (Set.singleton_subset_iff.mpr hW) hp
  obtain ⟨ω,hω⟩ := lemma_8 n hn W f (hbb W hW) hs (h0 W) T hT
  rw [hω,gwsvBasis]
  split
  · exact div_nonneg (ω.lam_pos i).le (Finset.sum_nonneg fun j _ => (ω.lam_pos j).le)
  · exact le_rfl

theorem twoEdgeProducts {n : ℕ} (hn : 1 < n) (V : Set (Welfare n))
    (f : Welfare n → Rule n) (hp : GuaranteesPNE V f)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W) (h0 : ∀ W i S, i ∉ S → f W i S = 0)
    {W Z : Welfare n} (hW : W ∈ V) (hZ : Z ∈ V) {i j : Fin n}
    {T U : Finset (Fin n)} (hT : T ∈ coalitionsPair W i j)
    (hU : U ∈ coalitionsPair Z j i) :
    basisRule (f W) W T i T * basisRule (f Z) Z U j U =
      basisRule (f W) W T j T * basisRule (f Z) Z U i U := by
  have hs : GuaranteesPNE {W,Z} f := by
    apply CostSharingIndexedAux.guarantees_mono f _ hp
    intro L hL
    rcases Set.mem_insert_iff.mp hL with h | h
    · exact h ▸ hW
    · exact (Set.mem_singleton_iff.mp h) ▸ hZ
  obtain ⟨hc,hj,hi⟩ := Finset.mem_filter.mp hU
  exact (lemma_9 n hn W Z f (hbb W hW) (hbb Z hZ) (h0 W) (h0 Z) hs
    i j T hT U (Finset.mem_filter.mpr ⟨hc,hi,hj⟩)).trans (mul_comm _ _)

end ShapleyCycleGame

namespace ShapleyCycleGame

theorem distinctCycleEquality {n k : ℕ} (hn : 1 < n) (hk : 3 ≤ k)
    (W : Fin k → Welfare n) (f : Welfare n → Rule n)
    (hbb : ∀ l, IsBudgetBalanced (f (W l)) (W l))
    (h0 : ∀ V i S, i ∉ S → f V i S = 0)
    (hp : GuaranteesPNE (Set.range W) f)
    (p : Fin k → Fin n) (pinj : Function.Injective p)
    (T : Fin k → Finset (Fin n))
    (hT : ∀ l, T l ∈ coalitionsPair (W l) (p l) (p (finRotate k l))) :
    (∏ l, basisRule (f (W l)) (W l) (T l) (p l) (T l)) =
      ∏ l, basisRule (f (W l)) (W l) (T l) (p (finRotate k l)) (T l) := by
  have hnneg (l : Fin k) (i : Fin n) :
      0 ≤ basisRule (f (W l)) (W l) (T l) i (T l) :=
    basisNonneg hn (Set.range W) f hp (fun _ ⟨j,hj⟩ => hj ▸ hbb j) h0
      ⟨l,rfl⟩ (Finset.mem_filter.mp (hT l)).1 i (T l)
  simpa only [abs_of_nonneg (hnneg _ _)] using
    distinctCycleProducts hn hk W f hbb h0 hp p pinj T hT

end ShapleyCycleGame

namespace ShapleyClosedWalk

/-- A closed walk may be partitioned at a repeated vertex.  Each edge index
belongs to precisely one of the two resulting closed walks. -/
theorem split_products {M : Type*} [CommMonoid M] {k a b : ℕ}
    (hab : a ≤ b) (hbk : b ≤ k) (f : ℕ → M) :
    (∏ j ∈ Finset.range k, f j) =
      (∏ j ∈ Finset.Ico a b, f j) *
        ((∏ j ∈ Finset.range a, f j) * (∏ j ∈ Finset.Ico b k, f j)) := by
  rw [← Finset.prod_range_mul_prod_Ico f (hab.trans hbk)]
  rw [← Finset.prod_Ico_consecutive f hab hbk]
  ac_rfl

end ShapleyClosedWalk

namespace ShapleyClosedWalk

/-- A property of edge products extends from simple closed walks to every
closed walk by cutting at two occurrences of the same vertex. -/
theorem closed_products {V E M : Type*} [CommMonoid M]
    (src dst : E → V) (L R : E → M)
    (simple : ∀ k (p : ℕ → V) (e : ℕ → E), p 0 = p k →
      (∀ j < k, src (e j) = p j ∧ dst (e j) = p (j+1)) →
      (∀ i < k, ∀ j < k, p i = p j → i = j) →
      (∏ j ∈ Finset.range k, L (e j)) = ∏ j ∈ Finset.range k, R (e j)) :
    ∀ k (p : ℕ → V) (e : ℕ → E), p 0 = p k →
      (∀ j < k, src (e j) = p j ∧ dst (e j) = p (j+1)) →
      (∏ j ∈ Finset.range k, L (e j)) = ∏ j ∈ Finset.range k, R (e j) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro p e hclose he
    by_cases hsimple : ∀ i < k, ∀ j < k, p i = p j → i = j
    · exact simple k p e hclose he hsimple
    push_neg at hsimple
    obtain ⟨a,ha,b,hb,hab,hn⟩ := hsimple
    have cut (a b : ℕ) (hab' : a < b) (hb' : b < k) (hp : p a = p b) :
        (∏ j ∈ Finset.range k, L (e j)) = ∏ j ∈ Finset.range k, R (e j) := by
      have hinner := ih (b-a) (by omega) (fun j => p (a+j)) (fun j => e (a+j))
        (by simpa [Nat.add_sub_of_le hab'.le] using hp)
        (fun j hj => by simpa [Nat.add_assoc] using he (a+j) (by omega))
      let shift := fun j => if j < a then j else j + (b-a)
      have hsa : shift a = b := by simp [shift, Nat.add_sub_of_le hab'.le]
      have hend : shift (k-(b-a)) = k := by dsimp [shift]; split <;> omega
      have hstart : p (shift 0) = p 0 := by
        by_cases hz : a = 0
        · subst a
          simpa [shift] using hp.symm
        · simp [shift, Nat.pos_of_ne_zero hz]
      have hout := ih (k-(b-a)) (by omega) (p ∘ shift) (e ∘ shift)
        (by simpa [Function.comp_def,hstart,hend] using hclose)
        (fun j hj => by
          simp only [Function.comp_apply]
          have hh := he (shift j) (by dsimp [shift]; split <;> omega)
          refine ⟨hh.1,hh.2.trans ?_⟩
          by_cases hj' : j < a
          · by_cases hh' : j+1 < a
            · simp [shift,hj',hh']
            · have hz : j+1 = a := by omega
              rw [hz,hsa]
              simpa [shift,hj',hz] using hp
          · have hj1 : ¬ j+1 < a := by omega
            simp only [shift,if_neg hj',if_neg hj1]
            congr 1
            omega)
      have translate (F : ℕ → M) :
          (∏ j ∈ Finset.range (k-(b-a)), F (shift j)) =
            (∏ j ∈ Finset.range a, F j) * ∏ j ∈ Finset.Ico b k, F j := by
        rw [← Finset.prod_range_mul_prod_Ico _ (show a ≤ k-(b-a) by omega)]
        congr 1
        · apply Finset.prod_congr rfl
          intro j hj
          simp [shift,Finset.mem_range.mp hj]
        · rw [Finset.prod_Ico_eq_prod_range, Finset.prod_Ico_eq_prod_range]
          have hlen : k-(b-a)-a = k-b := by omega
          rw [hlen]
          apply Finset.prod_congr rfl
          intro j _
          congr 1
          dsimp [shift]
          split <;> omega
      have houter : ((∏ j ∈ Finset.range a, L (e j)) * ∏ j ∈ Finset.Ico b k, L (e j)) =
          ((∏ j ∈ Finset.range a, R (e j)) * ∏ j ∈ Finset.Ico b k, R (e j)) := by
        rw [← translate (fun j => L (e j)),← translate (fun j => R (e j))]
        exact hout
      rw [split_products hab'.le hb'.le,split_products hab'.le hb'.le,houter]
      congr 1
      simpa only [Finset.prod_Ico_eq_prod_range,Nat.add_comm] using hinner
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact cut a b hlt hb hab
    · exact cut b a hgt ha hab.symm

end ShapleyClosedWalk

open CostSharingPNE.Char ShapleyCycleGame

private lemma nextVal {k : ℕ} (j : Fin k) :
    (finRotate k j).val = if j.val+1 < k then j.val+1 else 0 := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero j.neZero.ne
  rw [coe_finRotate]
  by_cases h : j = Fin.last m
  · subst j
    simp
  · rw [if_neg h,if_pos]
    have hv := Fin.val_lt_last h
    omega

private theorem allCycles {n : ℕ} (hn : 1 < n) (V : Set (Welfare n)) (f : Welfare n → Rule n)
    (hbb : ∀ W ∈ V, IsBudgetBalanced (f W) W)
    (h0 : ∀ W i S, i ∉ S → f W i S = 0) (hp : GuaranteesPNE V f)
    (k : ℕ) (p : ℕ → Fin n) (W : ℕ → Welfare n) (T : ℕ → Finset (Fin n))
    (hc : p 0 = p k)
    (he : ∀ j < k, W j ∈ V ∧ T j ∈ coalitionsPair (W j) (p j) (p (j+1))) :
    (∏ j ∈ Finset.range k, basisRule (f (W j)) (W j) (T j) (p j) (T j)) =
      ∏ j ∈ Finset.range k, basisRule (f (W j)) (W j) (T j) (p (j+1)) (T j) := by
  let E := {e : Welfare n × Finset (Fin n) × Fin n × Fin n //
    e.1 ∈ V ∧ e.2.1 ∈ coalitionsPair e.1 e.2.2.1 e.2.2.2}
  let src := fun e : E => e.1.2.2.1
  let dst := fun e : E => e.1.2.2.2
  let L := fun e : E => basisRule (f e.1.1) e.1.1 e.1.2.1 (src e) e.1.2.1
  let R := fun e : E => basisRule (f e.1.1) e.1.1 e.1.2.1 (dst e) e.1.2.1
  by_cases hk : 0 < k
  · let defaultEdge : E := ⟨(W 0,T 0,p 0,p 1),he 0 hk⟩
    let e := fun j => if h : j < k then (⟨(W j,T j,p j,p (j+1)),he j h⟩ : E) else defaultEdge
    have hh := ShapleyClosedWalk.closed_products src dst L R ?_ k p e hc (fun j hj => by simp [src,dst,e,hj])
    · exact (Finset.prod_congr rfl (fun j hj => by simp [L,src,e,Finset.mem_range.mp hj])).symm.trans
        (hh.trans (Finset.prod_congr rfl (fun j hj => by simp [R,dst,e,Finset.mem_range.mp hj])))
    · intro m q es hq hd hinj
      let w := fun l : Fin m => (es l.val).1.1
      let t := fun l : Fin m => (es l.val).1.2.1
      let v := fun l : Fin m => q l.val
      have hv : Function.Injective v := fun i j h => Fin.ext (hinj i i.isLt j j.isLt h)
      have hnext (l : Fin m) : v (finRotate m l) = q (l.val+1) := by
        change q (finRotate m l).val = _
        rw [nextVal]
        split
        · rfl
        · rename_i h
          rw [show l.val+1 = m by omega]
          exact hq
      have hT (l : Fin m) : t l ∈ coalitionsPair (w l) (v l) (v (finRotate m l)) := by
        rw [hnext]
        change (es l).1.2.1 ∈ coalitionsPair (es l).1.1 (q l) (q (l.val+1))
        rw [← (hd l l.isLt).1, ← (hd l l.isLt).2]
        exact (es l).2.2
      have hW (l : Fin m) : w l ∈ V := (es l).2.1
      have hP : GuaranteesPNE (Set.range w) f :=
        CostSharingIndexedAux.guarantees_mono f (fun _ ⟨l,hl⟩ => hl ▸ hW l) hp
      rw [← Fin.prod_univ_eq_prod_range,← Fin.prod_univ_eq_prod_range]
      have hl (j : Fin m) : L (es j) = basisRule (f (w j)) (w j) (t j) (v j) (t j) := by
        dsimp [L,w,t,v]
        rw [(hd j j.isLt).1]
      have hr (j : Fin m) : R (es j) = basisRule (f (w j)) (w j) (t j) (v (finRotate m j)) (t j) := by
        dsimp [R,w,t]
        rw [hnext,(hd j j.isLt).2]
      simp_rw [hl,hr]
      by_cases hm : 3 ≤ m
      · exact distinctCycleEquality hn hm w f (fun j => hbb _ (hW j)) h0 hP v hv t hT
      · have hm' : m = 0 ∨ m = 1 ∨ m = 2 := by omega
        rcases hm' with rfl | rfl | rfl
        · simp
        · have h : ∀ l : Fin 1, finRotate 1 l = l := fun l => Subsingleton.elim _ _
          simp_rw [h]
        · rw [Fin.prod_univ_two,Fin.prod_univ_two]
          change basisRule (f (w 0)) (w 0) (t 0) (v 0) (t 0) *
            basisRule (f (w 1)) (w 1) (t 1) (v 1) (t 1) =
            basisRule (f (w 0)) (w 0) (t 0) (v 1) (t 0) *
            basisRule (f (w 1)) (w 1) (t 1) (v 0) (t 1)
          exact twoEdgeProducts hn V f hp hbb h0 (hW 0) (hW 1) (hT 0) (hT 1)
  · have : k = 0 := by omega
    subst k
    simp

theorem solution (n : ℕ) (hn : 1 < n) (k : ℕ) (hk : 3 ≤ k) (W : Fin k → Welfare n)
    (f : Welfare n → Rule n)
    (hbb : ∀ l, IsBudgetBalanced (f (W l)) (W l))
    (h0 : ∀ l i S, i ∉ S → f (W l) i S = 0)
    (hpne : GuaranteesPNE (Set.range W) f)
    (p : Fin k → Fin n) (T : Fin k → Finset (Fin n))
    (hT : ∀ l, T l ∈ minimals (plusPair (f (W l)) (W l) (p l) (p (finRotate k l)))) :
    ∏ l, basisRule (f (W l)) (W l) (T l) (p l) (T l) =
      ∏ l, basisRule (f (W l)) (W l) (T l) (p (finRotate k l)) (T l) := by
  classical
  let w : ℕ → Welfare n := fun j => if h : j < k then W ⟨j,h⟩ else W ⟨0,by omega⟩
  let t : ℕ → Finset (Fin n) := fun j => if h : j < k then T ⟨j,h⟩ else ∅
  let v : ℕ → Fin n := fun j => if h : j < k then p ⟨j,h⟩ else p ⟨0,by omega⟩
  let g : Welfare n → Rule n := fun V i S => if V ∈ Set.range W then f V i S else 0
  classical
  have hG (l : Fin k) : g (W l) = f (W l) := by
    funext i S
    exact if_pos ⟨l,rfl⟩
  have hgp : GuaranteesPNE (Set.range W) g := by
    intro m hm V hV A hA
    obtain ⟨a,ha,hbest⟩ := hpne m hm V hV A hA
    refine ⟨a,ha,?_⟩
    have hu (b : Fin n → Finset (Fin m)) (i : Fin n) : utility V g b i = utility V f b i :=
      Finset.sum_congr rfl (fun r _ => if_pos (hV r))
    intro i b hb
    rw [hu,hu]
    exact hbest i b hb
  have hgb : ∀ V ∈ Set.range W, IsBudgetBalanced (g V) V := by
    rintro _ ⟨l,rfl⟩
    rw [hG]; exact hbb l
  have hg0 : ∀ V i S, i ∉ S → g V i S = 0 := by
    intro V i S hi
    by_cases h : V ∈ Set.range W
    · obtain ⟨l,rfl⟩ := h
      rw [hG]; exact h0 l i S hi
    · exact if_neg h
  have hnext (l : Fin k) : v (l.val+1) = p (finRotate k l) := by
    unfold v
    split
    · rename_i h
      congr 1
      apply Fin.ext
      rw [nextVal,if_pos h]
    · rename_i h
      congr 1
      apply Fin.ext
      rw [nextVal,if_neg h]
  have hh := allCycles hn (Set.range W) g hgb hg0 hgp k v w t
    (by simp [v,show 0 < k by omega]) (fun j hj => by
      let l : Fin k := ⟨j,hj⟩
      have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp (hT l)).1).1
      change w j ∈ Set.range W ∧ t j ∈ coalitionsPair (w j) (v j) (v (j+1))
      rw [show v (j+1) = p (finRotate k l) from hnext l]
      simpa [w,t,v,hj,l] using And.intro (show W l ∈ Set.range W from ⟨l,rfl⟩) hc)
  rw [← Fin.prod_univ_eq_prod_range,← Fin.prod_univ_eq_prod_range] at hh
  have hw (l : Fin k) : w l = W l := by simp [w,l.isLt]
  have ht (l : Fin k) : t l = T l := by simp [t,l.isLt]
  have hv (l : Fin k) : v l = p l := by simp [v,l.isLt]
  simpa only [hw,ht,hv,hnext,hG] using hh
