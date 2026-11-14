-- Prove2me | solution 1 for BorsukUlam.exists_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:21:11.13155+00:00
-- url     : https://prove2.me/submissions/76916460-a3b9-4531-9a8f-e270e65b8b7e

import Mathlib

section
noncomputable section
open Classical
namespace BorsukUlam.Dev
variable {n : ℕ}
/-!
# Borsuk–Ulam from Tucker's lemma (Freund–Todd), Blueprint

Tucker's lemma on the cube `[-m,m]^n`, triangulated by the reflected Kuhn (Freudenthal)
triangulation: a simplex is a nonempty set of grid points lying in one closed orthant whose
coordinatewise absolute values form a chain of diameter at most one.  The proof is the
Freund–Todd path-following argument: a graph on "happy" simplices in which `{0}` has degree one
and, absent a complementary edge, every other vertex has degree two.
-/
/-! ## The combinatorial setting -/
/-- A grid point of the cube `[-m,m]^n`. -/
def InBox (m : ℕ) (x : Fin n → ℤ) : Prop := ∀ i, |x i| ≤ m

/-- The grid points of the cube `[-m,m]^n`, as a finset. -/
def boxFinset (n m : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(m : ℤ)) m

/-- A simplex of the reflected Kuhn triangulation of `[-m,m]^n`. -/
def IsSimplex (m : ℕ) (σ : Finset (Fin n → ℤ)) : Prop :=
  σ.Nonempty ∧ (∀ x ∈ σ, InBox m x) ∧
  (∀ x ∈ σ, ∀ y ∈ σ, ∀ i, 0 ≤ x i * y i) ∧
  (∀ x ∈ σ, ∀ y ∈ σ, (∀ i, |x i| ≤ |y i|) ∨ (∀ i, |y i| ≤ |x i|)) ∧
  (∀ x ∈ σ, ∀ y ∈ σ, ∀ i, |x i| ≤ |y i| + 1)

/-- The signed coordinate directions of the smallest orthant face containing `σ`:
`sign(x_i) * (i+1)` over the points `x ∈ σ` and coordinates with `x_i ≠ 0`. -/
def signSet (σ : Finset (Fin n → ℤ)) : Finset ℤ :=
  σ.biUnion fun x =>
    (Finset.univ.filter fun i => x i ≠ 0).image fun i => Int.sign (x i) * ((i : ℤ) + 1)

/-- A happy simplex: its labels contain its sign set. -/
def Happy (m : ℕ) (lab : (Fin n → ℤ) → ℤ) (σ : Finset (Fin n → ℤ)) : Prop :=
  IsSimplex m σ ∧ signSet σ ⊆ σ.image lab

/-- `σ` lies in a facet `|x_a| = m` of the cube. -/
def OnBoundary (m : ℕ) (σ : Finset (Fin n → ℤ)) : Prop := ∃ a, ∀ x ∈ σ, |x a| = m

/-- Adjacency of the Freund–Todd graph (on happy simplices). -/
def Adj (m : ℕ) (lab : (Fin n → ℤ) → ℤ) (σ τ : Finset (Fin n → ℤ)) : Prop :=
  (∃ x ∈ σ, τ = σ.erase x ∧ signSet σ ⊆ τ.image lab) ∨
  (∃ x ∈ τ, σ = τ.erase x ∧ signSet τ ⊆ σ.image lab) ∨
  (τ = σ.image Neg.neg ∧ OnBoundary m σ ∧ σ.card = (signSet σ).card)

/-- The happy simplices, as a finset. -/
def happySet (n m : ℕ) (lab : (Fin n → ℤ) → ℤ) : Finset (Finset (Fin n → ℤ)) :=
  (boxFinset n m).powerset.filter fun σ => Happy m lab σ

/-- The neighbours of `σ` among the happy simplices. -/
def nbrs (m : ℕ) (lab : (Fin n → ℤ) → ℤ) (σ : Finset (Fin n → ℤ)) :
    Finset (Finset (Fin n → ℤ)) :=
  (happySet n m lab).filter fun τ => Adj m lab σ τ

/-- The standing hypotheses on the labelling. -/
structure GoodLabel (n m : ℕ) (lab : (Fin n → ℤ) → ℤ) : Prop where
  one_le : 1 ≤ m
  ne_zero : ∀ x : Fin n → ℤ, InBox m x → lab x ≠ 0
  abs_le : ∀ x : Fin n → ℤ, InBox m x → |lab x| ≤ n
  anti : ∀ x : Fin n → ℤ, InBox m x → (∃ a, |x a| = m) → lab (-x) = -lab x
  noComp : ∀ x y : Fin n → ℤ, InBox m x → InBox m y → (∀ i, |x i - y i| ≤ 1) →
    lab x + lab y ≠ 0

end BorsukUlam.Dev
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartThin
open BorsukUlam.Dev
variable {n : ℕ}
/-! ## Integer helpers -/
lemma coord_eq' {s t : ℤ} (h : |s| = |t|) (hst : 0 ≤ s * t) : s = t := by
  rcases abs_eq_abs.1 h with h1 | h1
  · exact h1
  · subst h1
    nlinarith [sq_nonneg t]

lemma coord_eq {s t u : ℤ} (h : |s| = |t|) (hs : 0 ≤ s * u) (ht : 0 ≤ t * u) (hu : u ≠ 0) :
    s = t := by
  rcases abs_eq_abs.1 h with h1 | h1
  · exact h1
  · subst h1
    have : t * u = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h2 | h2
    · simp [h2]
    · exact absurd h2 hu

lemma sign_cases {s : ℤ} (hs : s ≠ 0) : (0 < s ∧ Int.sign s = 1) ∨ (s < 0 ∧ Int.sign s = -1) := by
  rcases lt_or_gt_of_ne hs with h | h
  · exact Or.inr ⟨h, Int.sign_eq_neg_one_of_neg h⟩
  · exact Or.inl ⟨h, Int.sign_eq_one_of_pos h⟩

lemma sign_eq_of_mul_nonneg {s t : ℤ} (h : 0 ≤ s * t) (hs : s ≠ 0) (ht : t ≠ 0) :
    Int.sign s = Int.sign t := by
  rcases sign_cases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases sign_cases ht with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rw [h2, h4] <;> nlinarith

lemma sign_idx_inj {s t : ℤ} {i j : Fin n} (hs : s ≠ 0) (ht : t ≠ 0)
    (h : Int.sign s * ((i : ℤ) + 1) = Int.sign t * ((j : ℤ) + 1)) : i = j := by
  rcases sign_cases hs with ⟨-, h2⟩ | ⟨-, h2⟩ <;>
    rcases sign_cases ht with ⟨-, h4⟩ | ⟨-, h4⟩ <;> rw [h2, h4] at h <;>
    exact Fin.ext (by omega)

lemma abs_sub_sign {t : ℤ} (ht : t ≠ 0) : |t - Int.sign t| = |t| - 1 := by
  rcases sign_cases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
  · rw [abs_of_pos h1, abs_of_nonneg (by omega)]
  · rw [abs_of_neg h1, abs_of_nonpos (by omega)]; ring

lemma abs_add_sign {t : ℤ} (ht : t ≠ 0) : |t + Int.sign t| = |t| + 1 := by
  rcases sign_cases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
  · rw [abs_of_pos h1, abs_of_nonneg (by omega)]
  · rw [abs_of_neg h1, abs_of_nonpos (by omega)]; ring

lemma sub_sign_mul {t u : ℤ} (ht : t ≠ 0) (h : 0 ≤ t * u) : 0 ≤ (t - Int.sign t) * u := by
  rcases sign_cases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
  · have : 0 ≤ u := le_of_not_gt fun hc => by nlinarith
    nlinarith
  · have : u ≤ 0 := le_of_not_gt fun hc => by nlinarith
    nlinarith

lemma add_sign_mul {t u : ℤ} (ht : t ≠ 0) (h : 0 ≤ t * u) : 0 ≤ (t + Int.sign t) * u := by
  rcases sign_cases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
  · have : 0 ≤ u := le_of_not_gt fun hc => by nlinarith
    nlinarith
  · have : u ≤ 0 := le_of_not_gt fun hc => by nlinarith
    nlinarith

/-! ## Weights -/
/-- The weight `∑ |x i|`. -/
def wt (x : Fin n → ℤ) : ℤ := ∑ i, |x i|

lemma mem_boxFinset {m : ℕ} {x : Fin n → ℤ} : x ∈ boxFinset n m ↔ InBox m x := by
  simp [boxFinset, InBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

lemma mem_signSet {σ : Finset (Fin n → ℤ)} {e : ℤ} :
    e ∈ signSet σ ↔ ∃ x ∈ σ, ∃ i, x i ≠ 0 ∧ Int.sign (x i) * ((i : ℤ) + 1) = e := by
  simp [signSet]

/-- In a simplex, the coordinatewise order of absolute values follows the weight. -/
lemma le_of_wt_le {m : ℕ} {τ : Finset (Fin n → ℤ)} (hτ : IsSimplex m τ) {x y : Fin n → ℤ}
    (hx : x ∈ τ) (hy : y ∈ τ) (h : wt x ≤ wt y) : ∀ i, |x i| ≤ |y i| := by
  rcases hτ.2.2.2.1 x hx y hy with h1 | h1
  · exact h1
  · have hle : wt y ≤ wt x := Finset.sum_le_sum fun i _ => h1 i
    have heq := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) => h1 i)).1
      (le_antisymm hle h)
    intro i
    rw [heq i (Finset.mem_univ i)]

lemma eq_of_wt_eq {m : ℕ} {τ : Finset (Fin n → ℤ)} (hτ : IsSimplex m τ) {x y : Fin n → ℤ}
    (hx : x ∈ τ) (hy : y ∈ τ) (h : wt x = wt y) : x = y := by
  funext i
  exact coord_eq' (le_antisymm (le_of_wt_le hτ hx hy h.le i) (le_of_wt_le hτ hy hx h.ge i))
    (hτ.2.2.1 x hx y hy i)

/-! ## Simplex helpers -/
lemma isSimplex_insert {m : ℕ} {σ : Finset (Fin n → ℤ)} (hσ : IsSimplex m σ) {z : Fin n → ℤ}
    (hbox : InBox m z) (horth : ∀ y ∈ σ, ∀ i, 0 ≤ z i * y i)
    (hcmp : ∀ y ∈ σ, (∀ i, |z i| ≤ |y i|) ∨ (∀ i, |y i| ≤ |z i|))
    (hdiam : ∀ y ∈ σ, ∀ i, |z i| ≤ |y i| + 1 ∧ |y i| ≤ |z i| + 1) :
    IsSimplex m (insert z σ) := by
  obtain ⟨-, hB, hO, hC, hD⟩ := hσ
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.1 hx with h | h
    · rw [h]; exact hbox
    · exact hB x h
  · intro x hx y hy i
    rcases Finset.mem_insert.1 hx with h | h <;> rcases Finset.mem_insert.1 hy with h' | h'
    · rw [h, h']; exact mul_self_nonneg _
    · rw [h]; exact horth y h' i
    · rw [h', mul_comm]; exact horth x h i
    · exact hO x h y h' i
  · intro x hx y hy
    rcases Finset.mem_insert.1 hx with h | h <;> rcases Finset.mem_insert.1 hy with h' | h'
    · rw [h, h']; exact Or.inl fun i => le_rfl
    · rw [h]; exact hcmp y h'
    · rw [h']; exact (hcmp x h).symm
    · exact hC x h y h'
  · intro x hx y hy i
    rcases Finset.mem_insert.1 hx with h | h <;> rcases Finset.mem_insert.1 hy with h' | h'
    · rw [h, h']; linarith
    · rw [h]; exact (hdiam y h' i).1
    · rw [h']; exact (hdiam x h i).2
    · exact hD x h y h' i

lemma insert_between {m : ℕ} {σ : Finset (Fin n → ℤ)} (hσ : IsSimplex m σ)
    {z p q : Fin n → ℤ} (hp : p ∈ σ) (hq : q ∈ σ) (hz : ∀ i, z i = p i ∨ z i = q i)
    (hpz : ∀ i, |p i| ≤ |z i|) (hzq : ∀ i, |z i| ≤ |q i|)
    (hsep : ∀ y ∈ σ, (∀ i, |y i| ≤ |p i|) ∨ (∀ i, |q i| ≤ |y i|)) :
    IsSimplex m (insert z σ) := by
  refine isSimplex_insert hσ ?_ ?_ ?_ ?_
  · intro i
    rcases hz i with h | h <;> rw [h]
    · exact hσ.2.1 p hp i
    · exact hσ.2.1 q hq i
  · intro y hy i
    rcases hz i with h | h <;> rw [h]
    · exact hσ.2.2.1 p hp y hy i
    · exact hσ.2.2.1 q hq y hy i
  · intro y hy
    rcases hsep y hy with h | h
    · exact Or.inr fun i => (h i).trans (hpz i)
    · exact Or.inl fun i => (hzq i).trans (h i)
  · intro y hy i
    exact ⟨(hzq i).trans (hσ.2.2.2.2 q hq y hy i),
      (hσ.2.2.2.2 y hy p hp i).trans (by linarith [hpz i])⟩

lemma exists_lo {m : ℕ} {σ : Finset (Fin n → ℤ)} (hσ : IsSimplex m σ) :
    ∃ lo ∈ σ, ∀ y ∈ σ, ∀ i, |lo i| ≤ |y i| := by
  obtain ⟨lo, hlo, hmin⟩ := Finset.exists_min_image σ wt hσ.1
  exact ⟨lo, hlo, fun y hy => le_of_wt_le hσ hlo hy (hmin y hy)⟩

lemma exists_hi {m : ℕ} {σ : Finset (Fin n → ℤ)} (hσ : IsSimplex m σ) :
    ∃ hi ∈ σ, ∀ y ∈ σ, ∀ i, |y i| ≤ |hi i| := by
  obtain ⟨hi, hhi, hmax⟩ := Finset.exists_max_image σ wt hσ.1
  exact ⟨hi, hhi, fun y hy => le_of_wt_le hσ hy hhi (hmax y hy)⟩

lemma supp_hi {σ : Finset (Fin n → ℤ)} {hi : Fin n → ℤ}
    (hle_hi : ∀ y ∈ σ, ∀ i, |y i| ≤ |hi i|) {i : Fin n} {y : Fin n → ℤ} (hy : y ∈ σ)
    (hyi : y i ≠ 0) : hi i ≠ 0 := by
  intro h0
  have := hle_hi y hy i
  rw [h0, abs_zero] at this
  exact hyi (abs_nonpos_iff.1 this)

lemma signSet_eq {m : ℕ} {σ : Finset (Fin n → ℤ)} (hσ : IsSimplex m σ) {hi : Fin n → ℤ}
    (hhi : hi ∈ σ) (hle : ∀ y ∈ σ, ∀ i, |y i| ≤ |hi i|) :
    signSet σ = (Finset.univ.filter fun i => hi i ≠ 0).image
      fun i => Int.sign (hi i) * ((i : ℤ) + 1) := by
  ext e
  rw [mem_signSet, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, i, hxi, rfl⟩
    have h0 : hi i ≠ 0 := supp_hi hle hx hxi
    refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩, ?_⟩
    rw [sign_eq_of_mul_nonneg (hσ.2.2.1 x hx hi hhi i) hxi h0]
  · rintro ⟨i, hi', rfl⟩
    exact ⟨hi, hhi, i, (Finset.mem_filter.1 hi').2, rfl⟩

lemma card_signSet {m : ℕ} {σ : Finset (Fin n → ℤ)} (hσ : IsSimplex m σ) {hi : Fin n → ℤ}
    (hhi : hi ∈ σ) (hle : ∀ y ∈ σ, ∀ i, |y i| ≤ |hi i|) :
    (signSet σ).card = (Finset.univ.filter fun i => hi i ≠ 0).card := by
  rw [signSet_eq hσ hhi hle]
  apply Finset.card_image_of_injOn
  intro i hi' j hj' h
  exact sign_idx_inj (Finset.mem_filter.1 (Finset.mem_coe.1 hi')).2
    (Finset.mem_filter.1 (Finset.mem_coe.1 hj')).2 h

lemma exists_two {f : Fin n → ℤ} (h01 : ∀ i, f i = 0 ∨ f i = 1) (hsum : ∑ i, f i = 2) :
    ∃ a b, a ≠ b ∧ f a = 1 ∧ f b = 1 ∧ ∀ i, i ≠ a → i ≠ b → f i = 0 := by
  have hf : ∀ i, f i = if f i = 1 then 1 else 0 := by
    intro i
    rcases h01 i with h | h <;> simp [h]
  have hcard : (Finset.univ.filter (fun i => f i = 1)).card = 2 := by
    have : ∑ i, f i = ((Finset.univ.filter (fun i => f i = 1)).card : ℤ) := by
      rw [Finset.sum_congr rfl (fun i _ => hf i), Finset.sum_boole]
    omega
  obtain ⟨a, b, hab, hE⟩ := Finset.card_eq_two.1 hcard
  have hmem : ∀ i, f i = 1 ↔ i = a ∨ i = b := by
    intro i
    have : i ∈ Finset.univ.filter (fun i => f i = 1) ↔ i ∈ ({a, b} : Finset (Fin n)) := by
      rw [hE]
    simpa using this
  refine ⟨a, b, hab, (hmem a).2 (Or.inl rfl), (hmem b).2 (Or.inr rfl), ?_⟩
  intro i hia hib
  rcases h01 i with h | h
  · exact h
  · rcases (hmem i).1 h with h' | h'
    · exact absurd h' hia
    · exact absurd h' hib

lemma eq_update_of_abs {z p q : Fin n → ℤ} {a : Fin n} (hzp : ∀ i, 0 ≤ z i * p i)
    (hzq : ∀ i, 0 ≤ z i * q i) (ha : |z a| = |q a|) (hother : ∀ i, i ≠ a → |z i| = |p i|) :
    z = Function.update p a (q a) := by
  funext i
  by_cases h : i = a
  · subst h
    rw [Function.update_self]
    exact coord_eq' ha (hzq i)
  · rw [Function.update_of_ne h]
    exact coord_eq' (hother i h) (hzp i)

/-- A valid completion of `σ` to a larger simplex in the same orthant face. -/
def Valid (m : ℕ) (σ : Finset (Fin n → ℤ)) (z : Fin n → ℤ) : Prop :=
  z ∉ σ ∧ IsSimplex m (insert z σ) ∧ ∀ i, z i ≠ 0 → ∃ y ∈ σ, y i ≠ 0

/-! ## The label side -/
lemma mem_nbrs {m : ℕ} {lab : (Fin n → ℤ) → ℤ} {σ τ : Finset (Fin n → ℤ)} :
    τ ∈ nbrs m lab σ ↔ (τ ⊆ boxFinset n m ∧ Happy m lab τ) ∧ Adj m lab σ τ := by
  simp only [nbrs, happySet, Finset.mem_filter, Finset.mem_powerset]

lemma subset_box {m : ℕ} {τ : Finset (Fin n → ℤ)} (hτ : IsSimplex m τ) :
    τ ⊆ boxFinset n m :=
  fun x hx => mem_boxFinset.2 (hτ.2.1 x hx)

lemma signSet_insert_sub {m : ℕ} {σ : Finset (Fin n → ℤ)} {z : Fin n → ℤ}
    (hS : IsSimplex m (insert z σ)) (hsupp : ∀ i, z i ≠ 0 → ∃ y ∈ σ, y i ≠ 0) :
    signSet (insert z σ) ⊆ signSet σ := by
  intro e he
  rw [mem_signSet] at he ⊢
  obtain ⟨x, hx, i, hxi, rfl⟩ := he
  rcases Finset.mem_insert.1 hx with h | h
  · obtain ⟨y, hy, hyi⟩ := hsupp i (h ▸ hxi)
    refine ⟨y, hy, i, hyi, ?_⟩
    rw [sign_eq_of_mul_nonneg (hS.2.2.1 x hx y (Finset.mem_insert_of_mem hy) i) hxi hyi]
  · exact ⟨x, h, i, hxi, rfl⟩

lemma up_mem {m : ℕ} {lab : (Fin n → ℤ) → ℤ} {σ : Finset (Fin n → ℤ)} {z : Fin n → ℤ}
    (hσ : Happy m lab σ) (hv : Valid m σ z) : insert z σ ∈ nbrs m lab σ := by
  obtain ⟨hz, hS, hsupp⟩ := hv
  have hsl : signSet (insert z σ) ⊆ σ.image lab := (signSet_insert_sub hS hsupp).trans hσ.2
  rw [mem_nbrs]
  exact ⟨⟨subset_box hS, hS, hsl.trans (Finset.image_subset_image (Finset.subset_insert _ _))⟩,
    Or.inr (Or.inl ⟨z, Finset.mem_insert_self _ _, (Finset.erase_insert hz).symm, hsl⟩)⟩

lemma thin_image {m : ℕ} {lab : (Fin n → ℤ) → ℤ} {σ : Finset (Fin n → ℤ)}
    (hσ : Happy m lab σ) (hthin : σ.card = (signSet σ).card) : σ.image lab = signSet σ :=
  (Finset.eq_of_subset_of_card_le hσ.2 (Finset.card_image_le.trans hthin.le)).symm

lemma nbrs_cases {m : ℕ} {lab : (Fin n → ℤ) → ℤ} {σ τ : Finset (Fin n → ℤ)}
    (hσ : Happy m lab σ) (hthin : σ.card = (signSet σ).card) (hτ : τ ∈ nbrs m lab σ) :
    (∃ z, Valid m σ z ∧ τ = insert z σ) ∨ (τ = σ.image Neg.neg ∧ OnBoundary m σ) := by
  have himg := thin_image hσ hthin
  rw [mem_nbrs] at hτ
  obtain ⟨⟨-, hτS, -⟩, hadj⟩ := hτ
  rcases hadj with ⟨x, hx, rfl, hsub⟩ | ⟨x, hx, rfl, hsub⟩ | ⟨rfl, hb, -⟩
  · exfalso
    have h1 := Finset.card_le_card hsub
    have h2 : ((σ.erase x).image lab).card ≤ (σ.erase x).card := Finset.card_image_le
    have h3 := Finset.card_erase_of_mem hx
    have h4 : 0 < σ.card := Finset.card_pos.2 hσ.1.1
    omega
  · left
    refine ⟨x, ⟨Finset.notMem_erase x τ, by rwa [Finset.insert_erase hx], ?_⟩,
      (Finset.insert_erase hx).symm⟩
    intro i hxi
    have hmem : Int.sign (x i) * ((i : ℤ) + 1) ∈ signSet τ := mem_signSet.2 ⟨x, hx, i, hxi, rfl⟩
    rw [himg] at hsub
    obtain ⟨y, hy, j, hyj, hj⟩ := mem_signSet.1 (hsub hmem)
    have := sign_idx_inj hyj hxi hj
    subst this
    exact ⟨y, hy, hyj⟩
  · exact Or.inr ⟨rfl, hb⟩

lemma anti_mem {m : ℕ} {lab : (Fin n → ℤ) → ℤ} {σ : Finset (Fin n → ℤ)} (h : GoodLabel n m lab)
    (hσ : Happy m lab σ) (hthin : σ.card = (signSet σ).card) (hb : OnBoundary m σ) :
    σ.image Neg.neg ∈ nbrs m lab σ := by
  obtain ⟨a, ha⟩ := hb
  obtain ⟨⟨hne, hB, hO, hC, hD⟩, hsl⟩ := hσ
  have hS' : IsSimplex m (σ.image Neg.neg) := by
    refine ⟨hne.image _, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      intro i
      simpa using hB y hy i
    · intro x hx x' hx' i
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hx'
      simpa using hO y hy y' hy' i
    · intro x hx x' hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hx'
      simpa using hC y hy y' hy'
    · intro x hx x' hx' i
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hx'
      simpa using hD y hy y' hy' i
  rw [mem_nbrs]
  refine ⟨⟨subset_box hS', hS', ?_⟩, Or.inr (Or.inr ⟨rfl, ⟨a, ha⟩, hthin⟩)⟩
  intro e he
  obtain ⟨x, hx, i, hxi, rfl⟩ := mem_signSet.1 he
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
  have hyi : y i ≠ 0 := by simpa using hxi
  have hmem : Int.sign (y i) * ((i : ℤ) + 1) ∈ σ.image lab :=
    hsl (mem_signSet.2 ⟨y, hy, i, hyi, rfl⟩)
  obtain ⟨w, hw, hwl⟩ := Finset.mem_image.1 hmem
  refine Finset.mem_image.2 ⟨-w, Finset.mem_image.2 ⟨w, hw, rfl⟩, ?_⟩
  rw [h.anti w (hB w hw) ⟨a, ha w hw⟩, hwl]
  simp [Int.sign_neg]

lemma insert_ne_neg {m : ℕ} {σ : Finset (Fin n → ℤ)} {z : Fin n → ℤ} (hm : 1 ≤ m)
    (hS : IsSimplex m σ) (hb : OnBoundary m σ) : insert z σ ≠ σ.image Neg.neg := by
  intro heq
  obtain ⟨a, ha⟩ := hb
  obtain ⟨y, hy⟩ := hS.1
  have hy' : y ∈ σ.image Neg.neg := heq ▸ Finset.mem_insert_of_mem hy
  obtain ⟨x, hx, hxy⟩ := Finset.mem_image.1 hy'
  have h1 := hS.2.2.1 x hx y hy a
  have h2 := ha y hy
  rw [← hxy] at h1 h2
  simp only [Pi.neg_apply, abs_neg] at h1 h2
  have hx0 : x a = 0 := by
    by_contra hne
    have := mul_self_pos.2 hne
    linarith
  rw [hx0, abs_zero] at h2
  omega

/-! ## Case (a): the span is one on the whole support -/
lemma caseA_valid {m : ℕ} {σ : Finset (Fin n → ℤ)} (hS : IsSimplex m σ) {p q : Fin n → ℤ}
    (hp : p ∈ σ) (hq : q ∈ σ) {W : ℤ} (hpw : wt p = W - 1) (hnotW : ∀ y ∈ σ, wt y ≠ W)
    (hsep : ∀ y ∈ σ, (∀ i, |y i| ≤ |p i|) ∨ (∀ i, |q i| ≤ |y i|))
    (hpq : ∀ i, |p i| ≤ |q i|) {a : Fin n} (ha : |q a| = |p a| + 1) :
    Valid m σ (Function.update p a (q a)) := by
  have hz : ∀ i, Function.update p a (q a) i = p i ∨ Function.update p a (q a) i = q i := by
    intro i
    by_cases h : i = a
    · subst h; right; rw [Function.update_self]
    · left; rw [Function.update_of_ne h]
  have habs : ∀ i, |Function.update p a (q a) i| = |p i| + if i = a then 1 else 0 := by
    intro i
    by_cases h : i = a
    · subst h; rw [Function.update_self, if_pos rfl, ha]
    · rw [Function.update_of_ne h, if_neg h, add_zero]
  have hwt : wt (Function.update p a (q a)) = wt p + 1 := by
    unfold wt
    rw [Finset.sum_congr rfl (fun i _ => habs i), Finset.sum_add_distrib]
    simp
  refine ⟨fun hmem => hnotW _ hmem (by omega), ?_, ?_⟩
  · refine insert_between hS hp hq hz (fun i => ?_) (fun i => ?_) hsep
    · rw [habs i]; split_ifs <;> omega
    · rw [habs i]
      split_ifs with h
      · subst h; omega
      · simpa using hpq i
  · intro i hzi
    rcases hz i with h | h <;> rw [h] at hzi
    · exact ⟨p, hp, hzi⟩
    · exact ⟨q, hq, hzi⟩

lemma caseA {m : ℕ} {σ : Finset (Fin n → ℤ)} (hS : IsSimplex m σ) {lo hi : Fin n → ℤ}
    (hlo : lo ∈ σ) (hhi : hi ∈ σ) (hlo_le : ∀ y ∈ σ, ∀ i, |lo i| ≤ |y i|)
    (hle_hi : ∀ y ∈ σ, ∀ i, |y i| ≤ |hi i|)
    (hJ : ∀ i, hi i ≠ 0 → |hi i| = |lo i| + 1)
    (himg : σ.image wt ⊆ Finset.Icc (wt lo) (wt hi))
    (hcard : (σ.image wt).card + 1 = (Finset.Icc (wt lo) (wt hi)).card) :
    ∃ z1 z2, z1 ≠ z2 ∧ Valid m σ z1 ∧ Valid m σ z2 ∧ (∀ z, Valid m σ z → z = z1 ∨ z = z2) := by
  have hdiam : ∀ i, |hi i| ≤ |lo i| + 1 := fun i => hS.2.2.2.2 hi hhi lo hlo i
  obtain ⟨W, hWI, hWn⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card
      (show (σ.image wt).card < (Finset.Icc (wt lo) (wt hi)).card by omega)
  have himgeq : σ.image wt = (Finset.Icc (wt lo) (wt hi)).erase W := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      exact Finset.mem_erase.2 ⟨fun h => hWn (h ▸ hv), himg hv⟩
    · rw [Finset.card_erase_of_mem hWI]; omega
  have hget : ∀ V, wt lo ≤ V → V ≤ wt hi → V ≠ W → ∃ y ∈ σ, wt y = V := by
    intro V h1 h2 h3
    have : V ∈ σ.image wt := by
      rw [himgeq]; exact Finset.mem_erase.2 ⟨h3, Finset.mem_Icc.2 ⟨h1, h2⟩⟩
    simpa using this
  have hnotW : ∀ y ∈ σ, wt y ≠ W := fun y hy h => hWn (h ▸ Finset.mem_image_of_mem wt hy)
  have hWlo := hnotW lo hlo
  have hWhi := hnotW hi hhi
  obtain ⟨hW1, hW2⟩ := Finset.mem_Icc.1 hWI
  obtain ⟨p, hp, hpw⟩ := hget (W - 1) (by omega) (by omega) (by omega)
  obtain ⟨q, hq, hqw⟩ := hget (W + 1) (by omega) (by omega) (by omega)
  have hsep : ∀ y ∈ σ, (∀ i, |y i| ≤ |p i|) ∨ (∀ i, |q i| ≤ |y i|) := by
    intro y hy
    rcases lt_or_gt_of_ne (hnotW y hy) with h1 | h1
    · left; exact le_of_wt_le hS hy hp (by omega)
    · right; exact le_of_wt_le hS hq hy (by omega)
  have hpq : ∀ i, |p i| ≤ |q i| := le_of_wt_le hS hp hq (by omega)
  have hqp1 : ∀ i, |q i| ≤ |p i| + 1 := fun i => by
    linarith [hle_hi q hq i, hdiam i, hlo_le p hp i]
  have hsum : ∑ i, (|q i| - |p i|) = 2 := by
    rw [Finset.sum_sub_distrib]
    change wt q - wt p = 2
    omega
  obtain ⟨a, b, hab, ha, hb, hoth⟩ := exists_two (f := fun i => |q i| - |p i|)
    (fun i => by have := hpq i; have := hqp1 i; omega) hsum
  have hv1 := caseA_valid hS hp hq hpw hnotW hsep hpq (a := a) (by omega)
  have hv2 := caseA_valid hS hp hq hpw hnotW hsep hpq (a := b) (by omega)
  refine ⟨_, _, ?_, hv1, hv2, ?_⟩
  · intro heq
    have := congrFun heq b
    rw [Function.update_self, Function.update_of_ne (Ne.symm hab)] at this
    rw [this] at hb
    omega
  · rintro z ⟨hzn, hzS, hzsupp⟩
    have mz : z ∈ insert z σ := Finset.mem_insert_self _ _
    have mσ : ∀ y ∈ σ, y ∈ insert z σ := fun y hy => Finset.mem_insert_of_mem hy
    have hz0 : ∀ i, hi i = 0 → z i = 0 := by
      intro i h0
      by_contra hzi
      obtain ⟨y, hy, hyi⟩ := hzsupp i hzi
      exact supp_hi hle_hi hy hyi h0
    have hlo0 : ∀ i, hi i = 0 → lo i = 0 := by
      intro i h0
      by_contra hli
      exact supp_hi hle_hi hlo hli h0
    have h1 : wt lo < wt z := by
      by_contra hc
      have hle := le_of_wt_le hzS mz (mσ lo hlo) (not_lt.1 hc)
      apply hzn
      have : z = lo := by
        funext i
        refine coord_eq' ?_ (hzS.2.2.1 z mz lo (mσ lo hlo) i)
        by_cases h0 : hi i = 0
        · rw [hz0 i h0, hlo0 i h0]
        · have := hJ i h0
          have := hzS.2.2.2.2 hi (mσ hi hhi) z mz i
          have := hle i
          linarith
      rw [this]; exact hlo
    have h2 : wt z < wt hi := by
      by_contra hc
      have hle := le_of_wt_le hzS (mσ hi hhi) mz (not_lt.1 hc)
      apply hzn
      have : z = hi := by
        funext i
        refine coord_eq' ?_ (hzS.2.2.1 z mz hi (mσ hi hhi) i)
        by_cases h0 : hi i = 0
        · rw [hz0 i h0, h0]
        · have := hJ i h0
          have := hzS.2.2.2.2 z mz lo (mσ lo hlo) i
          have := hle i
          linarith
      rw [this]; exact hhi
    have hzW : wt z = W := by
      by_contra hne
      obtain ⟨y, hy, hyw⟩ := hget (wt z) h1.le h2.le hne
      exact hzn ((eq_of_wt_eq hzS mz (mσ y hy) hyw.symm) ▸ hy)
    have hpz := le_of_wt_le hzS (mσ p hp) mz (by omega)
    have hzq := le_of_wt_le hzS mz (mσ q hq) (by omega)
    have hzero : ∀ i, i ≠ a → i ≠ b → |z i| - |p i| = 0 := by
      intro i hia hib
      have := hoth i hia hib
      have := hpz i
      have := hzq i
      omega
    have hδ : ∑ i, (|z i| - |p i|) = (|z a| - |p a|) + (|z b| - |p b|) :=
      Fintype.sum_eq_add a b hab (fun i hi' => hzero i hi'.1 hi'.2)
    have hδ1 : ∑ i, (|z i| - |p i|) = 1 := by
      rw [Finset.sum_sub_distrib]
      change wt z - wt p = 1
      omega
    have hzp := fun i => hzS.2.2.1 z mz p (mσ p hp) i
    have hzq' := fun i => hzS.2.2.1 z mz q (mσ q hq) i
    have ha1 := hpz a
    have ha2 := hzq a
    have hb1 := hpz b
    have hb2 := hzq b
    by_cases hza : |z a| = |q a|
    · left
      refine eq_update_of_abs hzp hzq' hza (fun i hia => ?_)
      by_cases hib : i = b
      · subst hib; omega
      · have := hzero i hia hib; omega
    · right
      refine eq_update_of_abs hzp hzq' (by omega) (fun i hib => ?_)
      by_cases hia : i = a
      · subst hia; omega
      · have := hzero i hia hib; omega

/-! ## Case (b): one support coordinate is constant -/
lemma caseB {m : ℕ} {σ : Finset (Fin n → ℤ)} (hS : IsSimplex m σ) {lo hi : Fin n → ℤ}
    (hlo : lo ∈ σ) (hhi : hi ∈ σ) (hlo_le : ∀ y ∈ σ, ∀ i, |lo i| ≤ |y i|)
    (hle_hi : ∀ y ∈ σ, ∀ i, |y i| ≤ |hi i|) {a : Fin n}
    (ha : hi a ≠ 0) (haeq : |hi a| = |lo a|)
    (hJ : ∀ i, i ≠ a → hi i ≠ 0 → |hi i| = |lo i| + 1)
    (himg : σ.image wt = Finset.Icc (wt lo) (wt hi)) :
    Valid m σ (Function.update lo a (lo a - Int.sign (lo a))) ∧
    (|hi a| + 1 ≤ (m : ℤ) → Valid m σ (Function.update hi a (hi a + Int.sign (hi a)))) ∧
    (∀ z, Valid m σ z → z = Function.update lo a (lo a - Int.sign (lo a)) ∨
      (z = Function.update hi a (hi a + Int.sign (hi a)) ∧ |hi a| + 1 ≤ (m : ℤ))) := by
  have hdiam : ∀ i, |hi i| ≤ |lo i| + 1 := fun i => hS.2.2.2.2 hi hhi lo hlo i
  have hla : lo a ≠ 0 := by
    intro h0; rw [h0, abs_zero] at haeq; exact ha (abs_eq_zero.1 haeq)
  have hpos : 1 ≤ |lo a| := by
    have := abs_pos.2 hla; omega
  have hya : ∀ y ∈ σ, |y a| = |hi a| := fun y hy => by
    have := hlo_le y hy a; have := hle_hi y hy a; omega
  have hlobox := hS.2.1 lo hlo
  have hhibox := hS.2.1 hi hhi
  set z1 := Function.update lo a (lo a - Int.sign (lo a)) with hz1def
  set z2 := Function.update hi a (hi a + Int.sign (hi a)) with hz2def
  have hz1a : |z1 a| = |lo a| - 1 := by rw [hz1def, Function.update_self, abs_sub_sign hla]
  have hz2a : |z2 a| = |hi a| + 1 := by rw [hz2def, Function.update_self, abs_add_sign ha]
  have hz1o : ∀ i, i ≠ a → z1 i = lo i := fun i h => by rw [hz1def, Function.update_of_ne h]
  have hz2o : ∀ i, i ≠ a → z2 i = hi i := fun i h => by rw [hz2def, Function.update_of_ne h]
  have hz1a' : z1 a = lo a - Int.sign (lo a) := by rw [hz1def, Function.update_self]
  have hz2a' : z2 a = hi a + Int.sign (hi a) := by rw [hz2def, Function.update_self]
  refine ⟨⟨fun hmem => ?_, ?_, ?_⟩, fun hc => ⟨fun hmem => ?_, ?_, ?_⟩, ?_⟩
  · have := hya z1 hmem; omega
  · refine isSimplex_insert hS (fun i => ?_) (fun y hy i => ?_) (fun y hy => Or.inl fun i => ?_)
      (fun y hy i => ?_)
    · by_cases h : i = a
      · subst h; rw [hz1a]; have := hlobox i; omega
      · rw [hz1o i h]; exact hlobox i
    · by_cases h : i = a
      · subst h; rw [hz1a']; exact sub_sign_mul hla (hS.2.2.1 lo hlo y hy i)
      · rw [hz1o i h]; exact hS.2.2.1 lo hlo y hy i
    · by_cases h : i = a
      · subst h; rw [hz1a]; have := hlo_le y hy i; omega
      · rw [hz1o i h]; exact hlo_le y hy i
    · by_cases h : i = a
      · subst h; rw [hz1a]; have := hya y hy; omega
      · rw [hz1o i h]
        have := hlo_le y hy i; have := hle_hi y hy i; have := hdiam i
        constructor <;> linarith
  · intro i hzi
    by_cases h : i = a
    · subst h; exact ⟨hi, hhi, ha⟩
    · rw [hz1o i h] at hzi; exact ⟨lo, hlo, hzi⟩
  · have := hya z2 hmem; omega
  · refine isSimplex_insert hS (fun i => ?_) (fun y hy i => ?_) (fun y hy => Or.inr fun i => ?_)
      (fun y hy i => ?_)
    · by_cases h : i = a
      · subst h; rw [hz2a]; exact hc
      · rw [hz2o i h]; exact hhibox i
    · by_cases h : i = a
      · subst h; rw [hz2a']; exact add_sign_mul ha (hS.2.2.1 hi hhi y hy i)
      · rw [hz2o i h]; exact hS.2.2.1 hi hhi y hy i
    · by_cases h : i = a
      · subst h; rw [hz2a]; have := hle_hi y hy i; omega
      · rw [hz2o i h]; exact hle_hi y hy i
    · by_cases h : i = a
      · subst h; rw [hz2a]; have := hya y hy; omega
      · rw [hz2o i h]
        have := hlo_le y hy i; have := hle_hi y hy i; have := hdiam i
        constructor <;> linarith
  · intro i hzi
    by_cases h : i = a
    · subst h; exact ⟨hi, hhi, ha⟩
    · rw [hz2o i h] at hzi; exact ⟨hi, hhi, hzi⟩
  · rintro z ⟨hzn, hzS, hzsupp⟩
    have mz : z ∈ insert z σ := Finset.mem_insert_self _ _
    have mσ : ∀ y ∈ σ, y ∈ insert z σ := fun y hy => Finset.mem_insert_of_mem hy
    have hz0 : ∀ i, hi i = 0 → z i = 0 := by
      intro i h0
      by_contra hzi
      obtain ⟨y, hy, hyi⟩ := hzsupp i hzi
      exact supp_hi hle_hi hy hyi h0
    have hlo0 : ∀ i, hi i = 0 → lo i = 0 := by
      intro i h0
      by_contra hli
      exact supp_hi hle_hi hlo hli h0
    have hzlo := fun i => hzS.2.2.1 z mz lo (mσ lo hlo) i
    have hzhi := fun i => hzS.2.2.1 z mz hi (mσ hi hhi) i
    rcases lt_or_ge (wt z) (wt lo) with h1 | h1
    · -- below `lo`
      left
      have hle := le_of_wt_le hzS mz (mσ lo hlo) h1.le
      have hoth : ∀ i, i ≠ a → |z i| = |lo i| := by
        intro i hia
        by_cases h0 : hi i = 0
        · rw [hz0 i h0, hlo0 i h0]
        · have := hJ i hia h0
          have := hzS.2.2.2.2 hi (mσ hi hhi) z mz i
          have := hle i
          linarith
      have hza : |z a| = |lo a| - 1 := by
        have h3 := hzS.2.2.2.2 hi (mσ hi hhi) z mz a
        have h4 := hle a
        by_contra hne
        apply hzn
        have : z = lo := by
          funext i
          refine coord_eq' ?_ (hzlo i)
          by_cases hia : i = a
          · subst hia; omega
          · exact hoth i hia
        rw [this]; exact hlo
      funext i
      by_cases hia : i = a
      · subst hia
        refine coord_eq (u := lo i) (by rw [hza, hz1a]) (hzlo i) ?_ hla
        rw [hz1a']; exact sub_sign_mul hla (mul_self_nonneg _)
      · rw [hz1o i hia]; exact coord_eq' (hoth i hia) (hzlo i)
    rcases lt_or_ge (wt hi) (wt z) with h2 | h2
    · -- above `hi`
      right
      have hle := le_of_wt_le hzS (mσ hi hhi) mz h2.le
      have hoth : ∀ i, i ≠ a → |z i| = |hi i| := by
        intro i hia
        by_cases h0 : hi i = 0
        · rw [hz0 i h0, h0]
        · have := hJ i hia h0
          have := hzS.2.2.2.2 z mz lo (mσ lo hlo) i
          have := hle i
          linarith
      have hza : |z a| = |hi a| + 1 := by
        have h3 := hzS.2.2.2.2 z mz lo (mσ lo hlo) a
        have h4 := hle a
        by_contra hne
        apply hzn
        have : z = hi := by
          funext i
          refine coord_eq' ?_ (hzhi i)
          by_cases hia : i = a
          · subst hia; omega
          · exact hoth i hia
        rw [this]; exact hhi
      refine ⟨?_, by rw [← hza]; exact hzS.2.1 z mz a⟩
      funext i
      by_cases hia : i = a
      · subst hia
        refine coord_eq (u := hi i) (by rw [hza, hz2a]) (hzhi i) ?_ ha
        rw [hz2a']; exact add_sign_mul ha (mul_self_nonneg _)
      · rw [hz2o i hia]; exact coord_eq' (hoth i hia) (hzhi i)
    · exfalso
      have : wt z ∈ σ.image wt := by rw [himg]; exact Finset.mem_Icc.2 ⟨h1, h2⟩
      obtain ⟨y, hy, hyw⟩ := Finset.mem_image.1 this
      exact hzn ((eq_of_wt_eq hzS mz (mσ y hy) hyw.symm) ▸ hy)

/-! ## The geometric dichotomy for thin simplices -/
lemma geom {m : ℕ} (hm : 1 ≤ m) {σ : Finset (Fin n → ℤ)} (hS : IsSimplex m σ)
    (hk : σ.card = (signSet σ).card) :
    (∃ z1 z2, z1 ≠ z2 ∧ Valid m σ z1 ∧ Valid m σ z2 ∧ (∀ z, Valid m σ z → z = z1 ∨ z = z2) ∧
      ¬ OnBoundary m σ) ∨
    (∃ z1, Valid m σ z1 ∧ (∀ z, Valid m σ z → z = z1) ∧ OnBoundary m σ) := by
  obtain ⟨lo, hlo, hlo_le⟩ := exists_lo hS
  obtain ⟨hi, hhi, hle_hi⟩ := exists_hi hS
  have hdiam : ∀ i, |hi i| ≤ |lo i| + 1 := fun i => hS.2.2.2.2 hi hhi lo hlo i
  set J := Finset.univ.filter fun i => hi i ≠ 0 with hJdef
  set D := Finset.univ.filter fun i => |hi i| ≠ |lo i| with hDdef
  have hk' : σ.card = J.card := hk.trans (card_signSet hS hhi hle_hi)
  have hDJ : D ⊆ J := by
    intro i hi'
    have hi'' := (Finset.mem_filter.1 hi').2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun h0 => hi'' ?_⟩
    have h1 := hlo_le hi hhi i
    have h2 := abs_nonneg (lo i)
    rw [h0, abs_zero] at h1 ⊢
    linarith
  have hterm : ∀ i, |hi i| = |lo i| + if |hi i| ≠ |lo i| then (1 : ℤ) else 0 := by
    intro i
    have := hlo_le hi hhi i
    have := hdiam i
    split_ifs <;> omega
  have hwt : wt hi = wt lo + D.card := by
    calc wt hi = ∑ i, (|lo i| + if |hi i| ≠ |lo i| then (1 : ℤ) else 0) :=
          Finset.sum_congr rfl fun i _ => hterm i
      _ = wt lo + D.card := by rw [Finset.sum_add_distrib, Finset.sum_boole]; rfl
  have himg : σ.image wt ⊆ Finset.Icc (wt lo) (wt hi) := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hv
    exact Finset.mem_Icc.2 ⟨Finset.sum_le_sum fun i _ => hlo_le y hy i,
      Finset.sum_le_sum fun i _ => hle_hi y hy i⟩
  have hcardimg : (σ.image wt).card = σ.card :=
    Finset.card_image_of_injOn fun x hx y hy h => eq_of_wt_eq hS hx hy h
  have hIcc : (Finset.Icc (wt lo) (wt hi)).card = D.card + 1 := by
    rw [Int.card_Icc, hwt]
    omega
  have hcardle : σ.card ≤ D.card + 1 := by
    rw [← hcardimg, ← hIcc]; exact Finset.card_le_card himg
  have hDcard : D.card ≤ J.card := Finset.card_le_card hDJ
  have hmZ : (1 : ℤ) ≤ m := by exact_mod_cast hm
  by_cases hcase : D.card = J.card
  · -- case (a)
    have hDeq : D = J := Finset.eq_of_subset_of_card_le hDJ hcase.ge
    have hJ' : ∀ i, hi i ≠ 0 → |hi i| = |lo i| + 1 := by
      intro i h0
      have hiD : i ∈ D := by rw [hDeq]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩
      have := (Finset.mem_filter.1 hiD).2
      have := hlo_le hi hhi i
      have := hdiam i
      omega
    obtain ⟨z1, z2, hne, hv1, hv2, huniq⟩ :=
      caseA hS hlo hhi hlo_le hle_hi hJ' himg (by omega)
    refine Or.inl ⟨z1, z2, hne, hv1, hv2, huniq, ?_⟩
    rintro ⟨a, ha⟩
    have h1 := ha hi hhi
    have h2 := ha lo hlo
    have h0 : hi a ≠ 0 := by
      intro h0; rw [h0, abs_zero] at h1; omega
    have := hJ' a h0
    omega
  · -- case (b)
    have hcase' : D.card + 1 = J.card := by omega
    have hsd : (J \ D).card = 1 := by rw [Finset.card_sdiff_of_subset hDJ]; omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hsd
    have haJ : a ∈ J \ D := by rw [ha]; exact Finset.mem_singleton_self a
    have ha0 : hi a ≠ 0 := (Finset.mem_filter.1 (Finset.mem_sdiff.1 haJ).1).2
    have haeq : |hi a| = |lo a| := by
      by_contra hne
      exact (Finset.mem_sdiff.1 haJ).2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hne⟩)
    have hJ' : ∀ i, i ≠ a → hi i ≠ 0 → |hi i| = |lo i| + 1 := by
      intro i hia h0
      by_contra hne
      have hmem : i ∈ J \ D := by
        refine Finset.mem_sdiff.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩, fun h' => ?_⟩
        have h'' := (Finset.mem_filter.1 h').2
        have := hlo_le hi hhi i
        have := hdiam i
        exact hne (by omega)
      rw [ha] at hmem
      exact hia (Finset.mem_singleton.1 hmem)
    have himg' : σ.image wt = Finset.Icc (wt lo) (wt hi) :=
      Finset.eq_of_subset_of_card_le himg (by omega)
    obtain ⟨hv1, hv2, huniq⟩ := caseB hS hlo hhi hlo_le hle_hi ha0 haeq hJ' himg'
    have hya : ∀ y ∈ σ, |y a| = |hi a| := fun y hy => by
      have := hlo_le y hy a; have := hle_hi y hy a; omega
    by_cases hc : |hi a| + 1 ≤ (m : ℤ)
    · refine Or.inl ⟨_, _, ?_, hv1, hv2 hc, fun z hz => (huniq z hz).imp id And.left, ?_⟩
      · intro heq
        have := congrArg (fun f : Fin n → ℤ => |f a|) heq
        simp only [Function.update_self] at this
        have hla : lo a ≠ 0 := by
          intro h0; rw [h0, abs_zero] at haeq; exact ha0 (abs_eq_zero.1 haeq)
        rw [abs_sub_sign hla, abs_add_sign ha0] at this
        omega
      · rintro ⟨a', ha'⟩
        have h1 := ha' hi hhi
        have h2 := ha' lo hlo
        have h0 : hi a' ≠ 0 := by
          intro h0; rw [h0, abs_zero] at h1; omega
        by_cases haa : a' = a
        · subst haa; omega
        · have := hJ' a' haa h0; omega
    · refine Or.inr ⟨_, hv1, fun z hz => ?_, ⟨a, fun y hy => ?_⟩⟩
      · rcases huniq z hz with h' | h'
        · exact h'
        · exact absurd h'.2 hc
      · have := hS.2.1 hi hhi a
        rw [hya y hy]
        omega

/-! ## The target -/
theorem card_nbrs_thin (n m : ℕ) (lab : (Fin n → ℤ) → ℤ) (h : GoodLabel n m lab)
    (σ : Finset (Fin n → ℤ)) (hσ : Happy m lab σ) (hthin : σ.card = (signSet σ).card) :
    (nbrs m lab σ).card = 2 := by
  rcases geom h.one_le hσ.1 hthin with ⟨z1, z2, hne, hv1, hv2, huniq, hnb⟩ |
      ⟨z1, hv1, huniq, hb⟩
  · have hpair : nbrs m lab σ = {insert z1 σ, insert z2 σ} := by
      ext τ
      rw [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hτ
        rcases nbrs_cases hσ hthin hτ with ⟨z, hz, rfl⟩ | ⟨-, hb⟩
        · rcases huniq z hz with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · exact absurd hb hnb
      · rintro (rfl | rfl)
        · exact up_mem hσ hv1
        · exact up_mem hσ hv2
    rw [hpair, Finset.card_pair]
    intro heq
    have : z1 ∈ insert z2 σ := heq ▸ Finset.mem_insert_self z1 σ
    rcases Finset.mem_insert.1 this with h' | h'
    · exact hne h'
    · exact hv1.1 h'
  · have hpair : nbrs m lab σ = {insert z1 σ, σ.image Neg.neg} := by
      ext τ
      rw [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hτ
        rcases nbrs_cases hσ hthin hτ with ⟨z, hz, rfl⟩ | ⟨rfl, -⟩
        · exact Or.inl (by rw [huniq z hz])
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact up_mem hσ hv1
        · exact anti_mem h hσ hthin hb
    rw [hpair, Finset.card_pair (insert_ne_neg h.one_le hσ.1 hb)]

end BorsukUlam.Dev.PartThin
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev
variable {n : ℕ}
alias card_nbrs_thin := BorsukUlam.Dev.PartThin.card_nbrs_thin

end BorsukUlam.Dev
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartFull
open BorsukUlam.Dev
variable {n m : ℕ}
/-! ## Elementary facts about sign sets -/
theorem mem_signSet {σ : Finset (Fin n → ℤ)} {v : ℤ} :
    v ∈ signSet σ ↔ ∃ x ∈ σ, ∃ i, x i ≠ 0 ∧ Int.sign (x i) * ((i : ℤ) + 1) = v := by
  simp [signSet]

theorem signSet_mono {σ τ : Finset (Fin n → ℤ)} (h : σ ⊆ τ) : signSet σ ⊆ signSet τ := by
  intro v hv
  rw [mem_signSet] at hv ⊢
  obtain ⟨x, hx, i, hi, rfl⟩ := hv
  exact ⟨x, h hx, i, hi, rfl⟩

theorem abs_sign_mul {a : ℤ} (ha : a ≠ 0) (i : Fin n) :
    |Int.sign a * ((i : ℤ) + 1)| = (i : ℤ) + 1 := by
  rw [abs_mul, Int.abs_sign_of_ne_zero ha, one_mul, abs_of_pos (by positivity)]

theorem sign_mul_eq {a b : ℤ} {i i' : Fin n} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Int.sign a * ((i : ℤ) + 1) = Int.sign b * ((i' : ℤ) + 1)) :
    i = i' ∧ Int.sign a = Int.sign b := by
  have h1 : (i : ℤ) + 1 = (i' : ℤ) + 1 := by
    have := congrArg abs h
    rwa [abs_sign_mul ha, abs_sign_mul hb] at this
  have hii : i = i' := by ext; omega
  subst hii
  refine ⟨rfl, ?_⟩
  have : ((i : ℤ) + 1) ≠ 0 := by positivity
  exact mul_right_cancel₀ this h

theorem sign_cases {a : ℤ} (ha : a ≠ 0) : Int.sign a = 1 ∨ Int.sign a = -1 := by
  rcases lt_or_gt_of_ne ha with h | h
  · exact Or.inr (Int.sign_eq_neg_one_of_neg h)
  · exact Or.inl (Int.sign_eq_one_of_pos h)

theorem eq_sign_of_abs_le_one {a : ℤ} (ha : a ≠ 0) (h : |a| ≤ 1) : a = Int.sign a := by
  rw [abs_le] at h
  rcases lt_or_gt_of_ne ha with h' | h'
  · rw [Int.sign_eq_neg_one_of_neg h']; omega
  · rw [Int.sign_eq_one_of_pos h']; omega

theorem eq_of_abs_eq_of_mul_nonneg {a b : ℤ} (h : |a| = |b|) (h0 : 0 ≤ a * b) : a = b := by
  rcases abs_eq_abs.mp h with h3 | h3
  · exact h3
  · subst h3
    have : b * b = 0 := by nlinarith [mul_self_nonneg b]
    have hb : b = 0 := mul_self_eq_zero.mp this
    subst hb; simp

/-! ## The support -/
/-- The support of `σ`: coordinates on which some point of `σ` is nonzero. -/
def supp (σ : Finset (Fin n → ℤ)) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∃ x ∈ σ, x i ≠ 0

theorem mem_supp {σ : Finset (Fin n → ℤ)} {i : Fin n} : i ∈ supp σ ↔ ∃ x ∈ σ, x i ≠ 0 := by
  simp [supp]

theorem card_supp_le (σ : Finset (Fin n → ℤ)) : (supp σ).card ≤ (signSet σ).card := by
  calc (supp σ).card = ((supp σ).image fun i : Fin n => (i : ℤ) + 1).card := by
        refine (Finset.card_image_of_injective _ ?_).symm
        intro a b hab
        ext
        simp only at hab
        omega
    _ ≤ ((signSet σ).image abs).card := by
        refine Finset.card_le_card ?_
        intro v hv
        rw [Finset.mem_image] at hv ⊢
        obtain ⟨i, hi, rfl⟩ := hv
        obtain ⟨x, hx, hxi⟩ := mem_supp.mp hi
        exact ⟨Int.sign (x i) * ((i : ℤ) + 1), mem_signSet.mpr ⟨x, hx, i, hxi, rfl⟩,
          abs_sign_mul hxi i⟩
    _ ≤ _ := Finset.card_image_le

end BorsukUlam.Dev.PartFull
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartFull
open BorsukUlam.Dev
variable {n m : ℕ}
variable {σ : Finset (Fin n → ℤ)}
/-! ## Simplices -/
theorem eq_of_abs_eq (hσ : IsSimplex m σ) {x y : Fin n → ℤ} (hx : x ∈ σ) (hy : y ∈ σ)
    (h : ∀ i, |x i| = |y i|) : x = y := by
  funext i
  exact eq_of_abs_eq_of_mul_nonneg (h i) (hσ.2.2.1 x hx y hy i)

theorem abs_sub_le_one (hσ : IsSimplex m σ) {x y : Fin n → ℤ} (hx : x ∈ σ) (hy : y ∈ σ)
    (i : Fin n) : |x i - y i| ≤ 1 := by
  have h1 := hσ.2.2.1 x hx y hy i
  have h2 := hσ.2.2.2.2 x hx y hy i
  have h3 := hσ.2.2.2.2 y hy x hx i
  rw [abs_le]
  rcases le_total 0 (x i) with ha | ha <;> rcases le_total 0 (y i) with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb] at h2 h3; constructor <;> linarith
  · have : x i * y i = 0 := by nlinarith [mul_nonneg ha (neg_nonneg.mpr hb)]
    rcases mul_eq_zero.mp this with h | h
    · rw [h] at h3 ⊢; rw [abs_of_nonpos hb] at h3; simp at h3; constructor <;> linarith
    · rw [h] at h2 ⊢; rw [abs_of_nonneg ha] at h2; simp at h2; constructor <;> linarith
  · have : x i * y i = 0 := by nlinarith [mul_nonneg (neg_nonneg.mpr ha) hb]
    rcases mul_eq_zero.mp this with h | h
    · rw [h] at h3 ⊢; rw [abs_of_nonneg hb] at h3; simp at h3; constructor <;> linarith
    · rw [h] at h2 ⊢; rw [abs_of_nonpos ha] at h2; simp at h2; constructor <;> linarith
  · rw [abs_of_nonpos ha, abs_of_nonpos hb] at h2 h3; constructor <;> linarith

theorem isSimplex_of_subset (hσ : IsSimplex m σ) {τ : Finset (Fin n → ℤ)} (hτ : τ ⊆ σ)
    (hne : τ.Nonempty) : IsSimplex m τ :=
  ⟨hne, fun x hx => hσ.2.1 x (hτ hx), fun x hx y hy => hσ.2.2.1 x (hτ hx) y (hτ hy),
    fun x hx y hy => hσ.2.2.2.1 x (hτ hx) y (hτ hy),
    fun x hx y hy => hσ.2.2.2.2 x (hτ hx) y (hτ hy)⟩

theorem isSimplex_insert (hσ : IsSimplex m σ) {y : Fin n → ℤ} (hy : InBox m y)
    (horth : ∀ x ∈ σ, ∀ i, 0 ≤ x i * y i) (habove : ∀ x ∈ σ, ∀ i, |x i| ≤ |y i|)
    (hdiam : ∀ x ∈ σ, ∀ i, |y i| ≤ |x i| + 1) : IsSimplex m (insert y σ) := by
  refine ⟨Finset.insert_nonempty _ _, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with h1 | hx
    · rw [h1]; exact hy
    · exact hσ.2.1 x hx
  · intro x hx z hz i
    rcases Finset.mem_insert.mp hx with h1 | hx <;> rcases Finset.mem_insert.mp hz with h2 | hz
    · rw [h1, h2]; exact mul_self_nonneg _
    · rw [h1, mul_comm]; exact horth z hz i
    · rw [h2]; exact horth x hx i
    · exact hσ.2.2.1 x hx z hz i
  · intro x hx z hz
    rcases Finset.mem_insert.mp hx with h1 | hx <;> rcases Finset.mem_insert.mp hz with h2 | hz
    · rw [h1, h2]; exact Or.inl fun i => le_rfl
    · rw [h1]; exact Or.inr fun i => habove z hz i
    · rw [h2]; exact Or.inl fun i => habove x hx i
    · exact hσ.2.2.2.1 x hx z hz
  · intro x hx z hz i
    rcases Finset.mem_insert.mp hx with h1 | hx <;> rcases Finset.mem_insert.mp hz with h2 | hz
    · rw [h1, h2]; linarith
    · rw [h1]; exact hdiam z hz i
    · rw [h2]; linarith [habove x hx i]
    · exact hσ.2.2.2.2 x hx z hz i

/-- The potential `∑ |x i|`. -/
def pot (x : Fin n → ℤ) : ℤ := ∑ i, |x i|

theorem exists_bot (hσ : IsSimplex m σ) : ∃ x0 ∈ σ, ∀ x ∈ σ, ∀ i, |x0 i| ≤ |x i| := by
  obtain ⟨x0, hx0, hmin⟩ := σ.exists_min_image pot hσ.1
  refine ⟨x0, hx0, fun x hx => ?_⟩
  rcases hσ.2.2.2.1 x0 hx0 x hx with h | h
  · exact h
  · have hle : pot x ≤ pot x0 := Finset.sum_le_sum fun i _ => h i
    have heq : pot x = pot x0 := le_antisymm hle (hmin x hx)
    have := (Finset.sum_eq_sum_iff_of_le (fun i _ => h i)).mp heq
    intro i
    rw [this i (Finset.mem_univ _)]

/-- The chain count: `card σ ≤ card (signSet σ) + 1`, and in the equality case there is a top
point exceeding the bottom point by one on the whole support. -/
theorem chain_count (hσ : IsSimplex m σ) :
    σ.card ≤ (signSet σ).card + 1 ∧
    (σ.card = (signSet σ).card + 1 → ∃ x0 ∈ σ, ∃ t ∈ σ,
      (∀ x ∈ σ, ∀ i, |x0 i| ≤ |x i| ∧ |x i| ≤ |t i|) ∧ ∀ i ∈ supp σ, |t i| = |x0 i| + 1) := by
  obtain ⟨x0, hx0, hbot⟩ := exists_bot hσ
  let D : (Fin n → ℤ) → Finset (Fin n) := fun x => Finset.univ.filter fun i => |x i| ≠ |x0 i|
  have hmemD : ∀ x i, i ∈ D x ↔ |x i| ≠ |x0 i| := fun x i => by simp [D]
  -- value of `|x i|` in terms of `D x`
  have hval : ∀ x ∈ σ, ∀ i, |x i| = |x0 i| + if i ∈ D x then 1 else 0 := by
    intro x hx i
    have h1 := hbot x hx i
    have h2 := hσ.2.2.2.2 x hx x0 hx0 i
    by_cases hi : i ∈ D x
    · rw [if_pos hi]; rw [hmemD] at hi; omega
    · rw [if_neg hi]; rw [hmemD] at hi; push Not at hi; omega
  have hDsupp : ∀ x ∈ σ, D x ⊆ supp σ := by
    intro x hx i hi
    rw [hmemD] at hi
    refine mem_supp.mpr ⟨x, hx, fun h0 => hi ?_⟩
    have := hbot x hx i
    rw [h0, abs_zero] at this ⊢
    exact le_antisymm (abs_nonneg _) this
  have hDinj : ∀ x ∈ σ, ∀ y ∈ σ, D x = D y → x = y := by
    intro x hx y hy hD
    refine eq_of_abs_eq hσ hx hy fun i => ?_
    rw [hval x hx i, hval y hy i, hD]
  have hDmono : ∀ x ∈ σ, ∀ y ∈ σ, (∀ i, |x i| ≤ |y i|) → D x ⊆ D y := by
    intro x hx y hy hxy i hi
    rw [hmemD] at hi ⊢
    have := hbot x hx i
    have := hxy i
    omega
  have hinj : Set.InjOn (fun x => (D x).card) σ := by
    intro x hx y hy hxy
    simp only at hxy
    apply hDinj x hx y hy
    rcases hσ.2.2.2.1 x hx y hy with h | h
    · exact Finset.eq_of_subset_of_card_le (hDmono x hx y hy h) hxy.ge
    · exact (Finset.eq_of_subset_of_card_le (hDmono y hy x hx h) hxy.le).symm
  have himg : σ.image (fun x => (D x).card) ⊆ Finset.range ((supp σ).card + 1) := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_range]
    have := Finset.card_le_card (hDsupp x hx)
    omega
  have hcard : σ.card ≤ (supp σ).card + 1 := by
    have := Finset.card_le_card himg
    rw [Finset.card_image_of_injOn hinj, Finset.card_range] at this
    exact this
  have hss := card_supp_le σ
  refine ⟨by omega, fun heq => ?_⟩
  have himg' : σ.image (fun x => (D x).card) = Finset.range ((supp σ).card + 1) := by
    refine Finset.eq_of_subset_of_card_le himg ?_
    rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    omega
  have : (supp σ).card ∈ σ.image (fun x => (D x).card) := by
    rw [himg']; exact Finset.self_mem_range_succ _
  obtain ⟨t, ht, htcard⟩ := Finset.mem_image.mp this
  have hDt : D t = supp σ := Finset.eq_of_subset_of_card_le (hDsupp t ht) htcard.ge
  have htop : ∀ i ∈ supp σ, |t i| = |x0 i| + 1 := by
    intro i hi
    rw [hval t ht i, if_pos (hDt ▸ hi)]
  refine ⟨x0, hx0, t, ht, fun x hx i => ⟨hbot x hx i, ?_⟩, htop⟩
  by_cases hi : i ∈ supp σ
  · rw [htop i hi]; exact hσ.2.2.2.2 x hx x0 hx0 i
  · have : x i = 0 := by
      by_contra hne; exact hi (mem_supp.mpr ⟨x, hx, hne⟩)
    rw [this, abs_zero]; exact abs_nonneg _

end BorsukUlam.Dev.PartFull
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartFull
open BorsukUlam.Dev
variable {n m : ℕ}
/-! ## Combinatorics of a labelling with one collision -/
theorem card_filter_dup {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α)
    (f : α → β) (h : (s.image f).card + 1 = s.card) :
    (s.filter fun x => ∃ z ∈ s, z ≠ x ∧ f z = f x).card = 2 := by
  have hni : ¬ Set.InjOn f s := by
    intro hinj
    rw [Finset.card_image_of_injOn hinj] at h
    omega
  obtain ⟨a, ha, b, hb, hab, hne⟩ : ∃ a ∈ s, ∃ b ∈ s, f a = f b ∧ a ≠ b := by
    by_contra hcon
    push Not at hcon
    exact hni fun a ha b hb hab => hcon a ha b hb hab
  have : (s.filter fun x => ∃ z ∈ s, z ≠ x ∧ f z = f x) = {a, b} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, z, hz, hzx, hfz⟩
      by_contra hxab
      push Not at hxab
      -- the image is covered by `s` minus `a` and `x`
      have hsub : s.image f ⊆ ((s.erase a).erase x).image f := by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
        rw [Finset.mem_image]
        by_cases hwa : w = a
        · subst hwa
          exact ⟨b, Finset.mem_erase.mpr ⟨hxab.2.symm, Finset.mem_erase.mpr ⟨hne.symm, hb⟩⟩,
            hab.symm⟩
        by_cases hwx : w = x
        · subst hwx
          by_cases hza : z = a
          · subst hza
            exact ⟨b, Finset.mem_erase.mpr ⟨hxab.2.symm, Finset.mem_erase.mpr ⟨hne.symm, hb⟩⟩,
              by rw [← hfz, hab]⟩
          · exact ⟨z, Finset.mem_erase.mpr ⟨hzx, Finset.mem_erase.mpr ⟨hza, hz⟩⟩, hfz⟩
        · exact ⟨w, Finset.mem_erase.mpr ⟨hwx, Finset.mem_erase.mpr ⟨hwa, hw⟩⟩, rfl⟩
      have h1 := Finset.card_le_card hsub
      have h2 := Finset.card_image_le (s := (s.erase a).erase x) (f := f)
      have h3 : ((s.erase a).erase x).card = s.card - 2 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxab.1, hx⟩),
          Finset.card_erase_of_mem ha]
        omega
      have h4 : 2 ≤ s.card := by
        have := Finset.card_le_card (show ({a, b} : Finset α) ⊆ s by
          intro v hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
          rcases hv with rfl | rfl <;> assumption)
        rwa [Finset.card_pair hne] at this
      omega
    · rintro (h1 | h1)
      · rw [h1]; exact ⟨ha, b, hb, hne.symm, hab.symm⟩
      · rw [h1]; exact ⟨hb, a, ha, hne, hab⟩
  rw [this, Finset.card_pair hne]

end BorsukUlam.Dev.PartFull
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartFull
open BorsukUlam.Dev
variable {n m : ℕ}
variable {lab : (Fin n → ℤ) → ℤ}
/-! ## Membership in `nbrs` -/
theorem mem_boxFinset {x : Fin n → ℤ} : x ∈ boxFinset n m ↔ InBox m x := by
  simp [boxFinset, InBox, Fintype.mem_piFinset, abs_le]

theorem mem_happySet {τ : Finset (Fin n → ℤ)} : τ ∈ happySet n m lab ↔ Happy m lab τ := by
  simp only [happySet, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun h => h.2
  · intro h; exact ⟨fun x hx => mem_boxFinset.mpr (h.1.2.1 x hx), h⟩

theorem mem_nbrs {σ τ : Finset (Fin n → ℤ)} :
    τ ∈ nbrs m lab σ ↔ Happy m lab τ ∧ Adj m lab σ τ := by
  simp only [nbrs, Finset.mem_filter, mem_happySet]

theorem down_mem {σ : Finset (Fin n → ℤ)} (hσ : Happy m lab σ) {x : Fin n → ℤ} (hx : x ∈ σ)
    (hne : (σ.erase x).Nonempty) (hS : signSet σ ⊆ (σ.erase x).image lab) :
    σ.erase x ∈ nbrs m lab σ := by
  refine mem_nbrs.mpr ⟨⟨isSimplex_of_subset hσ.1 (Finset.erase_subset _ _) hne,
    (signSet_mono (Finset.erase_subset _ _)).trans hS⟩, Or.inl ⟨x, hx, rfl, hS⟩⟩

theorem up_mem {σ τ : Finset (Fin n → ℤ)} (hτ : Happy m lab τ) {x : Fin n → ℤ} (hx : x ∈ τ)
    (he : σ = τ.erase x) (hS : signSet τ ⊆ σ.image lab) : τ ∈ nbrs m lab σ :=
  mem_nbrs.mpr ⟨hτ, Or.inr (Or.inl ⟨x, hx, he, hS⟩)⟩

/-- An up-neighbour of a full simplex forces `card (lab σ) = card σ` and `signSet τ = lab σ`. -/
theorem up_card {σ τ : Finset (Fin n → ℤ)} (hτ : IsSimplex m τ) {x : Fin n → ℤ} (hx : x ∈ τ)
    (he : σ = τ.erase x) (hS : signSet τ ⊆ σ.image lab) :
    (σ.image lab).card = σ.card ∧ signSet τ = σ.image lab := by
  have h1 := (chain_count hτ).1
  have h2 : σ.card + 1 = τ.card := by
    rw [he, Finset.card_erase_of_mem hx]
    have := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have h3 := Finset.card_le_card hS
  have h4 := Finset.card_image_le (s := σ) (f := lab)
  refine ⟨by omega, Finset.eq_of_subset_of_card_le hS (by omega)⟩

end BorsukUlam.Dev.PartFull
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartFull
open BorsukUlam.Dev
variable {n m : ℕ}
variable {lab : (Fin n → ℤ) → ℤ} {σ : Finset (Fin n → ℤ)}
/-! ## Full happy simplices -/
theorem full_card (hσ : Happy m lab σ) (hfull : σ.card ≠ (signSet σ).card) :
    σ.card = (signSet σ).card + 1 := by
  have h1 := (chain_count hσ.1).1
  have h2 := Finset.card_le_card hσ.2
  have h3 := Finset.card_image_le (s := σ) (f := lab)
  omega

/-- Case (i): the labels of `σ` are exactly its sign set. -/
theorem card_nbrs_caseI (hσ : Happy m lab σ) (hfull : σ.card = (signSet σ).card + 1)
    (hL : (σ.image lab).card ≠ σ.card) : (nbrs m lab σ).card = 2 := by
  have hSL : signSet σ = σ.image lab := by
    have h3 := Finset.card_image_le (s := σ) (f := lab)
    exact Finset.eq_of_subset_of_card_le hσ.2 (by omega)
  have hdup : (σ.image lab).card + 1 = σ.card := by
    have h3 := Finset.card_image_le (s := σ) (f := lab)
    rw [← hSL]; omega
  have heq : nbrs m lab σ =
      (σ.filter fun x => ∃ z ∈ σ, z ≠ x ∧ lab z = lab x).image (σ.erase ·) := by
    ext τ
    rw [Finset.mem_image]
    constructor
    · intro hτ
      obtain ⟨hτh, hadj⟩ := mem_nbrs.mp hτ
      rcases hadj with ⟨x, hx, rfl, hS⟩ | ⟨x, hx, he, hS⟩ | ⟨-, -, hc⟩
      · refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩, rfl⟩
        have : lab x ∈ signSet σ := hSL ▸ Finset.mem_image_of_mem lab hx
        obtain ⟨z, hz, hzl⟩ := Finset.mem_image.mp (hS this)
        exact ⟨z, Finset.mem_of_mem_erase hz, Finset.ne_of_mem_erase hz, hzl⟩
      · exact absurd (up_card hτh.1 hx he hS).1 hL
      · omega
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hx, z, hz, hzx, hzl⟩ := Finset.mem_filter.mp hx
      refine down_mem hσ hx ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩⟩ ?_
      rw [hSL]
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      rw [Finset.mem_image]
      by_cases hwx : w = x
      · subst hwx; exact ⟨z, Finset.mem_erase.mpr ⟨hzx, hz⟩, hzl⟩
      · exact ⟨w, Finset.mem_erase.mpr ⟨hwx, hw⟩, rfl⟩
  rw [heq, Finset.card_image_of_injOn, card_filter_dup σ lab hdup]
  intro x hx x' hx' hxx
  simp only at hxx
  by_contra hne
  have : x' ∈ σ.erase x :=
    Finset.mem_erase.mpr ⟨Ne.symm hne, (Finset.mem_filter.mp hx').1⟩
  rw [hxx] at this
  exact Finset.notMem_erase _ _ this

/-- Case (ii): `lab σ = signSet σ ∪ {ℓ}`; exactly one up-neighbour and at most one
down-neighbour. -/
theorem nbrs_caseII (h : GoodLabel n m lab) (hσ : Happy m lab σ)
    (hfull : σ.card = (signSet σ).card + 1) (hL : (σ.image lab).card = σ.card) :
    ∃ a ∈ σ, ∃ y, y ∉ σ ∧ ∀ τ, τ ∈ nbrs m lab σ ↔
      ((τ = σ.erase a ∧ (σ.erase a).Nonempty) ∨ τ = insert y σ) := by
  set S := signSet σ with hSdef
  set L := σ.image lab with hLdef
  have hinj : Set.InjOn lab σ := Finset.card_image_iff.mp hL
  have hSL : S ⊆ L := hσ.2
  have hcard1 : (L \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hSL]; omega
  obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hcard1
  have hℓL : ℓ ∈ L := (Finset.mem_sdiff.mp (hℓ ▸ Finset.mem_singleton_self ℓ)).1
  have hℓS : ℓ ∉ S := (Finset.mem_sdiff.mp (hℓ ▸ Finset.mem_singleton_self ℓ)).2
  have hLcases : ∀ v ∈ L, v = ℓ ∨ v ∈ S := by
    intro v hv
    by_cases hvS : v ∈ S
    · exact Or.inr hvS
    · left
      have : v ∈ L \ S := Finset.mem_sdiff.mpr ⟨hv, hvS⟩
      rw [hℓ] at this
      exact Finset.mem_singleton.mp this
  obtain ⟨a, ha, hla⟩ := Finset.mem_image.mp hℓL
  have hbox : ∀ x ∈ σ, InBox m x := hσ.1.2.1
  have hℓ0 : ℓ ≠ 0 := hla ▸ h.ne_zero a (hbox a ha)
  have hℓn : |ℓ| ≤ n := hla ▸ h.abs_le a (hbox a ha)
  -- the coordinate `j` of `ℓ`
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (j : ℤ) + 1 = |ℓ| := by
    have h1 : (ℓ.natAbs : ℤ) = |ℓ| := Int.natCast_natAbs ℓ
    have h2 : ℓ.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hℓ0
    refine ⟨⟨ℓ.natAbs - 1, by omega⟩, ?_⟩
    simp only
    omega
  have hℓj : Int.sign ℓ * ((j : ℤ) + 1) = ℓ := by rw [hj, Int.sign_mul_abs]
  -- `-ℓ ∉ S` by `noComp`
  have hnegS : -ℓ ∉ S := by
    intro hm
    obtain ⟨z, hz, hzl⟩ := Finset.mem_image.mp (hSL hm)
    exact h.noComp z a (hbox z hz) (hbox a ha) (fun i => abs_sub_le_one hσ.1 hz ha i)
      (by rw [hzl, hla]; ring)
  -- `j` is outside the support
  have hjsupp : ∀ x ∈ σ, x j = 0 := by
    intro x hx
    by_contra hxj
    have hv : Int.sign (x j) * ((j : ℤ) + 1) ∈ S := mem_signSet.mpr ⟨x, hx, j, hxj, rfl⟩
    rcases sign_cases hxj with h1 | h1 <;> rcases sign_cases hℓ0 with h2 | h2
    · apply hℓS; rw [← hℓj, h2]; rw [h1] at hv; exact hv
    · apply hnegS; rw [← hℓj, h2]; rw [h1] at hv; convert hv using 1; ring
    · apply hnegS; rw [← hℓj, h2]; rw [h1] at hv; convert hv using 1; ring
    · apply hℓS; rw [← hℓj, h2]; rw [h1] at hv; exact hv
  -- bottom and top
  obtain ⟨x0, hx0, t, ht, hchain, htop⟩ := (chain_count hσ.1).2 hfull
  let y : Fin n → ℤ := Function.update t j (Int.sign ℓ)
  have hyj : y j = Int.sign ℓ := Function.update_self _ _ _
  have hyi : ∀ i, i ≠ j → y i = t i := fun i hi => Function.update_of_ne hi _ _
  have hsignℓ : |Int.sign ℓ| = 1 := Int.abs_sign_of_ne_zero hℓ0
  have hyσ : y ∉ σ := by
    intro hy
    have := hjsupp y hy
    rw [hyj] at this
    exact hℓ0 (Int.sign_eq_zero_iff_zero.mp this)
  -- the up-neighbour is a simplex
  have hysimp : IsSimplex m (insert y σ) := by
    refine isSimplex_insert hσ.1 ?_ ?_ ?_ ?_
    · intro i
      by_cases hij : i = j
      · subst hij; rw [hyj, hsignℓ]; exact_mod_cast h.one_le
      · rw [hyi i hij]; exact hbox t ht i
    · intro x hx i
      by_cases hij : i = j
      · subst hij; rw [hjsupp x hx]; simp
      · rw [hyi i hij]; exact hσ.1.2.2.1 x hx t ht i
    · intro x hx i
      by_cases hij : i = j
      · subst hij; rw [hjsupp x hx]; simp
      · rw [hyi i hij]; exact (hchain x hx i).2
    · intro x hx i
      by_cases hij : i = j
      · subst hij; rw [hjsupp x hx, hyj, hsignℓ]; simp
      · rw [hyi i hij]; exact hσ.1.2.2.2.2 t ht x hx i
  have hyS : signSet (insert y σ) ⊆ L := by
    intro v hv
    obtain ⟨z, hz, i, hzi, rfl⟩ := mem_signSet.mp hv
    rcases Finset.mem_insert.mp hz with rfl | hz
    · by_cases hij : i = j
      · subst hij; rw [hyj, Int.sign_sign, hℓj]; exact hℓL
      · rw [hyi i hij] at hzi ⊢
        exact hSL (mem_signSet.mpr ⟨t, ht, i, hzi, rfl⟩)
    · exact hSL (mem_signSet.mpr ⟨z, hz, i, hzi, rfl⟩)
  refine ⟨a, ha, y, hyσ, fun τ => ⟨fun hτ => ?_, fun hτ => ?_⟩⟩
  · obtain ⟨hτh, hadj⟩ := mem_nbrs.mp hτ
    rcases hadj with ⟨x, hx, rfl, hS⟩ | ⟨x, hx, he, hS⟩ | ⟨-, -, hc⟩
    · -- down-neighbour: `x = a`
      left
      have hne := hτh.1.1
      suffices hxa : x = a by subst hxa; exact ⟨rfl, hne⟩
      have hxS : lab x ∉ S := by
        intro hm
        obtain ⟨z, hz, hzl⟩ := Finset.mem_image.mp (hS hm)
        exact Finset.ne_of_mem_erase hz (hinj (Finset.mem_of_mem_erase hz) hx hzl)
      rcases hLcases (lab x) (Finset.mem_image_of_mem lab hx) with h1 | h1
      · exact hinj hx ha (h1.trans hla.symm)
      · exact absurd h1 hxS
    · -- up-neighbour: `x = y`
      right
      have hτeq : τ = insert x σ := by rw [he, Finset.insert_erase hx]
      have hxσ : x ∉ σ := by rw [he]; exact Finset.notMem_erase _ _
      obtain ⟨-, hτL⟩ := up_card hτh.1 hx he hS
      have hτs := hτh.1
      rw [hτeq] at hτs hτL
      have hmx : x ∈ insert x σ := Finset.mem_insert_self _ _
      -- coordinate `j`
      have hℓτ : ℓ ∈ signSet (insert x σ) := by rw [hτL]; exact hℓL
      obtain ⟨z, hz, i0, hzi0, hzl⟩ := mem_signSet.mp hℓτ
      have hzx : z = x := by
        rcases Finset.mem_insert.mp hz with h1 | h1
        · exact h1
        · exact absurd (mem_signSet.mpr ⟨z, h1, i0, hzi0, hzl⟩) hℓS
      rw [hzx] at hzi0 hzl
      rw [← hℓj] at hzl
      obtain ⟨rfl, hsg⟩ := sign_mul_eq hzi0 hℓ0 hzl
      have hx0τ : x0 ∈ insert x σ := Finset.mem_insert_of_mem hx0
      have htτ : t ∈ insert x σ := Finset.mem_insert_of_mem ht
      have hxj : x i0 = y i0 := by
        have h1 := hτs.2.2.2.2 x hmx x0 hx0τ i0
        rw [hjsupp x0 hx0, abs_zero, zero_add] at h1
        rw [hyj, eq_sign_of_abs_le_one hzi0 h1, hsg]
      have habove : ∀ i, |t i| ≤ |x i| := by
        rcases hτs.2.2.2.1 x hmx t htτ with h1 | h1
        · exfalso
          have := h1 i0
          rw [hjsupp t ht, abs_zero] at this
          exact hzi0 (abs_nonpos_iff.mp this)
        · exact h1
      have hxy : x = y := by
        funext i
        by_cases hij : i = i0
        · subst hij; exact hxj
        rw [hyi i hij]
        by_cases hi : i ∈ supp σ
        · have h1 := hτs.2.2.2.2 x hmx x0 hx0τ i
          rw [← htop i hi] at h1
          exact eq_of_abs_eq_of_mul_nonneg (le_antisymm h1 (habove i))
            (hτs.2.2.1 x hmx t htτ i)
        · have ht0 : t i = 0 := by
            by_contra hne; exact hi (mem_supp.mpr ⟨t, ht, hne⟩)
          rw [ht0]
          by_contra hxi
          have hv : Int.sign (x i) * ((i : ℤ) + 1) ∈ signSet (insert x σ) :=
            mem_signSet.mpr ⟨x, hmx, i, hxi, rfl⟩
          rw [hτL] at hv
          rcases hLcases _ hv with h1 | h1
          · rw [← hℓj] at h1
            exact hij (sign_mul_eq hxi hℓ0 h1).1
          · obtain ⟨w, hw, i', hwi, hwl⟩ := mem_signSet.mp h1
            obtain ⟨rfl, -⟩ := sign_mul_eq hwi hxi hwl
            exact hi (mem_supp.mpr ⟨w, hw, hwi⟩)
      rw [hτeq, hxy]
    · have : σ.card = S.card := hc
      omega
  · rcases hτ with ⟨rfl, hne⟩ | rfl
    · refine down_mem hσ ha hne ?_
      intro v hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hSL hv)
      refine Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨?_, hw⟩, rfl⟩
      rintro rfl
      exact hℓS (hla ▸ hv)
    · refine up_mem ⟨hysimp, hyS.trans (Finset.image_subset_image (Finset.subset_insert _ _))⟩
        (Finset.mem_insert_self y σ) (Finset.erase_insert hyσ).symm ?_
      exact hyS

end BorsukUlam.Dev.PartFull
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartFull
open BorsukUlam.Dev
variable {n m : ℕ}
/-! ## The targets -/
/-- Every other happy simplex with no complementary edge has exactly two neighbours:
full simplices (`card = card signSet + 1`), other than `{0}`. -/
theorem card_nbrs_full (n m : ℕ) (lab : (Fin n → ℤ) → ℤ) (h : GoodLabel n m lab)
    (σ : Finset (Fin n → ℤ)) (hσ : Happy m lab σ) (hfull : σ.card ≠ (signSet σ).card)
    (h0 : σ ≠ {0}) :
    (nbrs m lab σ).card = 2 := by
  have hf := full_card hσ hfull
  by_cases hL : (σ.image lab).card = σ.card
  · obtain ⟨a, ha, y, hyσ, hchar⟩ := nbrs_caseII h hσ hf hL
    have hne : (σ.erase a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      rcases (Finset.erase_eq_empty_iff σ a).mp he with h1 | h1
      · rw [h1] at ha; simp at ha
      · apply h0
        rw [h1] at hf ⊢
        have hS : signSet ({a} : Finset (Fin n → ℤ)) = ∅ := by
          rw [Finset.card_singleton] at hf
          exact Finset.card_eq_zero.mp (by omega)
        congr 1
        funext i
        by_contra hai
        have : Int.sign (a i) * ((i : ℤ) + 1) ∈ signSet ({a} : Finset (Fin n → ℤ)) :=
          mem_signSet.mpr ⟨a, Finset.mem_singleton_self a, i, hai, rfl⟩
        rw [hS] at this; simp at this
    have heq : nbrs m lab σ = {σ.erase a, insert y σ} := by
      ext τ
      rw [hchar τ, Finset.mem_insert, Finset.mem_singleton]
      simp only [hne, and_true]
    rw [heq, Finset.card_pair]
    intro hc
    have : a ∈ σ.erase a := by rw [hc]; exact Finset.mem_insert_of_mem ha
    exact Finset.notMem_erase _ _ this
  · exact card_nbrs_caseI hσ hf hL

/-- `{0}` has exactly one neighbour. -/
theorem card_nbrs_zero (n m : ℕ) (lab : (Fin n → ℤ) → ℤ) (h : GoodLabel n m lab) :
    (nbrs m lab {0}).card = 1 := by
  have hS : signSet ({0} : Finset (Fin n → ℤ)) = ∅ := by
    ext v; simp [mem_signSet]
  have hσ : Happy m lab {0} := by
    refine ⟨⟨Finset.singleton_nonempty _, ?_, ?_, ?_, ?_⟩, by rw [hS]; exact Finset.empty_subset _⟩
    all_goals simp [InBox]
  have hf : ({0} : Finset (Fin n → ℤ)).card = (signSet ({0} : Finset (Fin n → ℤ))).card + 1 := by
    rw [hS]; simp
  have hL : (({0} : Finset (Fin n → ℤ)).image lab).card = ({0} : Finset (Fin n → ℤ)).card := by
    simp
  obtain ⟨a, ha, y, -, hchar⟩ := nbrs_caseII h hσ hf hL
  rw [Finset.mem_singleton] at ha
  subst ha
  have heq : nbrs m lab {0} = {insert y {0}} := by
    ext τ
    rw [hchar τ, Finset.mem_singleton]
    simp
  rw [heq, Finset.card_singleton]

end BorsukUlam.Dev.PartFull
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev
variable {n : ℕ}
/-! ## Stubs: the degree count -/
alias card_nbrs_zero := BorsukUlam.Dev.PartFull.card_nbrs_zero

alias card_nbrs_full := BorsukUlam.Dev.PartFull.card_nbrs_full

end BorsukUlam.Dev
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev.PartG
open BorsukUlam.Dev
variable {n : ℕ}
lemma mem_boxFinset {m : ℕ} {x : Fin n → ℤ} : x ∈ boxFinset n m ↔ InBox m x := by
  simp [boxFinset, InBox, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

lemma mem_signSet {σ : Finset (Fin n → ℤ)} {e : ℤ} :
    e ∈ signSet σ ↔ ∃ x ∈ σ, ∃ i, x i ≠ 0 ∧ Int.sign (x i) * ((i : ℤ) + 1) = e := by
  simp [signSet]

lemma signSet_neg (σ : Finset (Fin n → ℤ)) :
    signSet (σ.image Neg.neg) = (signSet σ).image Neg.neg := by
  ext e
  simp only [mem_signSet, Finset.mem_image]
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, i, hi, rfl⟩
    refine ⟨Int.sign (x i) * ((i : ℤ) + 1), ⟨x, hx, i, ?_, rfl⟩, ?_⟩
    · simpa using hi
    · simp [Int.sign_neg]
  · rintro ⟨e', ⟨x, hx, i, hi, rfl⟩, rfl⟩
    refine ⟨-x, ⟨x, hx, rfl⟩, i, by simpa using hi, ?_⟩
    simp [Int.sign_neg]

lemma card_signSet_neg (σ : Finset (Fin n → ℤ)) :
    (signSet (σ.image Neg.neg)).card = (signSet σ).card := by
  rw [signSet_neg, Finset.card_image_of_injective _ neg_injective]

lemma adj_symm {m : ℕ} {lab : (Fin n → ℤ) → ℤ} {σ τ : Finset (Fin n → ℤ)}
    (h : Adj m lab σ τ) : Adj m lab τ σ := by
  rcases h with h | h | ⟨rfl, ⟨a, ha⟩, hc⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · refine Or.inr (Or.inr ⟨?_, ⟨a, ?_⟩, ?_⟩)
    · rw [Finset.image_image]; simp
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
      simpa using ha x hx
    · rw [card_signSet_neg, Finset.card_image_of_injective _ neg_injective, hc]

lemma not_adj_self {m : ℕ} (hm : 1 ≤ m) {lab : (Fin n → ℤ) → ℤ} {σ : Finset (Fin n → ℤ)}
    (hσ : Happy m lab σ) : ¬ Adj m lab σ σ := by
  rintro (⟨x, hx, h, -⟩ | ⟨x, hx, h, -⟩ | ⟨h, ⟨a, ha⟩, -⟩)
  · exact (Finset.erase_eq_self.1 h.symm) hx
  · exact (Finset.erase_eq_self.1 h.symm) hx
  · obtain ⟨x, hx⟩ := hσ.1.1
    have hnx : -x ∈ σ := by
      rw [h]; exact Finset.mem_image.2 ⟨x, hx, rfl⟩
    have h1 := hσ.1.2.2.1 x hx (-x) hnx a
    have h2 := ha x hx
    simp only [Pi.neg_apply, mul_neg] at h1
    have h3 : x a * x a ≤ 0 := by linarith
    have h4 : x a = 0 := by nlinarith [mul_self_nonneg (x a)]
    rw [h4] at h2
    simp at h2
    omega

lemma zero_mem_happySet {m : ℕ} {lab : (Fin n → ℤ) → ℤ} :
    ({0} : Finset (Fin n → ℤ)) ∈ happySet n m lab := by
  have hbox : InBox m (0 : Fin n → ℤ) := fun i => by simp
  have hsign : signSet ({0} : Finset (Fin n → ℤ)) = ∅ := by
    ext e; simp [mem_signSet]
  unfold happySet
  rw [Finset.mem_filter, Finset.mem_powerset]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.1 hx]
    exact mem_boxFinset.2 hbox
  · refine ⟨Finset.singleton_nonempty _, ?_, ?_, ?_, ?_⟩ <;> simp [hbox]
  · rw [hsign]; exact Finset.empty_subset _

theorem not_goodLabel (n m : ℕ) (lab : (Fin n → ℤ) → ℤ) : ¬ GoodLabel n m lab := by
  intro h
  set H := happySet n m lab with hH
  have happy_of_mem : ∀ σ ∈ H, Happy m lab σ := fun σ hσ => (Finset.mem_filter.1 hσ).2
  let G : SimpleGraph {σ // σ ∈ H} :=
    { Adj := fun s t => Adj m lab s.1 t.1
      symm := ⟨fun s t hst => adj_symm hst⟩
      loopless := ⟨fun (s : {σ // σ ∈ H}) hs => not_adj_self h.one_le (happy_of_mem s.1 s.2) hs⟩ }
  have hdeg : ∀ s : {σ // σ ∈ H}, G.degree s = (nbrs m lab s.1).card := by
    intro s
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : nbrs m lab s.1 = (G.neighborFinset s).map (Function.Embedding.subtype _) := by
      ext τ
      simp only [nbrs, Finset.mem_filter, Finset.mem_map, SimpleGraph.mem_neighborFinset,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨hτ, hadj⟩
        exact ⟨⟨τ, hτ⟩, hadj, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.2, ht⟩
    rw [this, Finset.card_map]
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg] at hsum
  rw [Finset.sum_coe_sort H (fun σ => (nbrs m lab σ).card)] at hsum
  have h0 : ({0} : Finset (Fin n → ℤ)) ∈ H := zero_mem_happySet
  rw [← Finset.add_sum_erase _ _ h0] at hsum
  have hrest : ∑ σ ∈ H.erase {0}, (nbrs m lab σ).card = ∑ σ ∈ H.erase {0}, 2 := by
    apply Finset.sum_congr rfl
    intro σ hσ
    obtain ⟨hne, hσH⟩ := Finset.mem_erase.1 hσ
    by_cases hthin : σ.card = (signSet σ).card
    · exact BorsukUlam.Dev.card_nbrs_thin n m lab h σ (happy_of_mem σ hσH) hthin
    · exact BorsukUlam.Dev.card_nbrs_full n m lab h σ (happy_of_mem σ hσH) hthin hne
  rw [hrest, BorsukUlam.Dev.card_nbrs_zero n m lab h, Finset.sum_const, smul_eq_mul] at hsum
  omega

end BorsukUlam.Dev.PartG
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.Dev
variable {n : ℕ}
alias not_goodLabel := BorsukUlam.Dev.PartG.not_goodLabel

/-- Tucker's lemma on the cube `[-m,m]^n`. -/
theorem tucker (n m : ℕ) (hm : 1 ≤ m) (lab : (Fin n → ℤ) → ℤ)
    (hlab : ∀ x : Fin n → ℤ, InBox m x → lab x ≠ 0 ∧ |lab x| ≤ n)
    (hanti : ∀ x : Fin n → ℤ, InBox m x → (∃ a, |x a| = m) → lab (-x) = -lab x) :
    ∃ x y : Fin n → ℤ, InBox m x ∧ InBox m y ∧ (∀ i, |x i - y i| ≤ 1) ∧ lab x + lab y = 0 := by
  by_contra hne
  push_neg at hne
  exact not_goodLabel n m lab
    ⟨hm, fun x hx => (hlab x hx).1, fun x hx => (hlab x hx).2, hanti, hne⟩

end BorsukUlam.Dev
end
end

section
noncomputable section
open Classical
namespace BorsukUlam.PartBU
open BorsukUlam.Dev
/-! ## The map from the cube `[-1,1]^d` to the sphere -/
/-- The vector `(u, 1 - ‖u‖∞)`. -/
def rawVec {d : ℕ} (u : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  fun j => if h : (j : ℕ) < d then u ⟨j, h⟩ else 1 - ‖u‖

lemma rawVec_cont (d : ℕ) : Continuous (rawVec (d := d)) := by
  refine continuous_pi fun j => ?_
  by_cases h : (j : ℕ) < d
  · simp only [rawVec, h, dif_pos]
    exact continuous_apply _
  · simp only [rawVec, h, dif_neg, not_false_eq_true]
    exact continuous_const.sub continuous_norm

lemma rawVec_ne {d : ℕ} (u : Fin d → ℝ) : rawVec u ≠ 0 := by
  intro h
  have hu : u = 0 := by
    funext i
    have := congrFun h ⟨i, by omega⟩
    simpa [rawVec, i.isLt] using this
  have := congrFun h (Fin.last d)
  simp [rawVec, hu] at this

lemma rawVec_neg {d : ℕ} (u : Fin d → ℝ) (hu : ‖u‖ = 1) : rawVec (-u) = -rawVec u := by
  funext j
  by_cases h : (j : ℕ) < d
  · simp [rawVec, h]
  · simp [rawVec, h, hu]

/-- `(u, 1 - ‖u‖∞)` as a Euclidean vector. -/
def wVec {d : ℕ} (u : Fin d → ℝ) : EuclideanSpace ℝ (Fin (d + 1)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm (rawVec u)

lemma wVec_cont (d : ℕ) : Continuous (wVec (d := d)) :=
  (EuclideanSpace.equiv (Fin (d + 1)) ℝ).symm.continuous.comp (rawVec_cont d)

lemma wVec_ne {d : ℕ} (u : Fin d → ℝ) : wVec u ≠ 0 := by
  intro h
  apply rawVec_ne u
  have := congrArg (EuclideanSpace.equiv (Fin (d + 1)) ℝ) h
  simpa [wVec] using this

lemma wVec_neg {d : ℕ} (u : Fin d → ℝ) (hu : ‖u‖ = 1) : wVec (-u) = -wVec u := by
  simp [wVec, rawVec_neg u hu]

/-- The normalized vector, a point of the sphere. -/
def phi {d : ℕ} (u : Fin d → ℝ) : Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1 :=
  ⟨‖wVec u‖⁻¹ • wVec u, by
    simp [norm_smul, norm_ne_zero_iff.2 (wVec_ne u)]⟩

lemma phi_cont (d : ℕ) : Continuous (phi (d := d)) :=
  Continuous.subtype_mk (((wVec_cont d).norm.inv₀ fun u => norm_ne_zero_iff.2 (wVec_ne u)).smul
    (wVec_cont d)) _

lemma phi_neg {d : ℕ} (u : Fin d → ℝ) (hu : ‖u‖ = 1) : phi (-u) = -phi u := by
  apply Subtype.ext
  simp [phi, wVec_neg u hu]

/-! ## Labels -/
/-- Indices where `|v i| ≥ δ`. -/
def idxSet {d : ℕ} (δ : ℝ) (v : Fin d → ℝ) : Finset (Fin d) :=
  Finset.univ.filter fun i => δ ≤ |v i|

/-- The label: sign of `v i` times `i + 1`, for the least index `i` with `|v i| ≥ δ`. -/
def labOf {d : ℕ} (δ : ℝ) (v : Fin d → ℝ) : ℤ :=
  if h : (idxSet δ v).Nonempty then
    (if 0 < v ((idxSet δ v).min' h) then 1 else -1) * ((((idxSet δ v).min' h : ℕ) : ℤ) + 1)
  else 0

lemma idxSet_neg {d : ℕ} (δ : ℝ) (v : Fin d → ℝ) : idxSet δ (-v) = idxSet δ v := by
  ext i
  simp [idxSet, abs_neg]

lemma labOf_neg {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (v : Fin d → ℝ) : labOf δ (-v) = -labOf δ v := by
  unfold labOf
  rw [idxSet_neg]
  by_cases h : (idxSet δ v).Nonempty
  · rw [dif_pos h, dif_pos h]
    have hi : δ ≤ |v ((idxSet δ v).min' h)| :=
      (Finset.mem_filter.1 (Finset.min'_mem _ h)).2
    have hne : v ((idxSet δ v).min' h) ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hi
      linarith
    simp only [Pi.neg_apply, neg_pos]
    split_ifs with h1 h2 h2
    · linarith
    · ring
    · ring
    · exact absurd (le_antisymm (not_lt.1 h2) (not_lt.1 h1)) hne
  · rw [dif_neg h, dif_neg h, neg_zero]

lemma labOf_spec {d : ℕ} {δ : ℝ} (v : Fin d → ℝ) (h : ∃ i, δ ≤ |v i|) :
    ∃ i : Fin d, labOf δ v = (if 0 < v i then 1 else -1) * (((i : ℕ) : ℤ) + 1) ∧
      δ ≤ |v i| := by
  have hne : (idxSet δ v).Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, by simp [idxSet, hi]⟩
  refine ⟨(idxSet δ v).min' hne, ?_, (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2⟩
  simp only [labOf, dif_pos hne]

/-! ## Borsuk–Ulam -/
theorem exists_eq_neg_dev (d : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, EuclideanSpace ℝ (Fin d))) :
    ∃ x, f x = f (-x) := by
  by_contra hne
  push Not at hne
  set e := EuclideanSpace.equiv (Fin d) ℝ
  let G : (Fin d → ℝ) → (Fin d → ℝ) := fun u => e (f (phi u) - f (-phi u))
  have hG : Continuous G := e.continuous.comp
    ((f.continuous.comp (phi_cont d)).sub (f.continuous.comp (phi_cont d).neg))
  have hG0 : ∀ u, G u ≠ 0 := by
    intro u h
    apply hne (phi u)
    have : f (phi u) - f (-phi u) = 0 := by
      apply e.injective
      simpa [G] using h
    exact sub_eq_zero.1 this
  have hGneg : ∀ u : Fin d → ℝ, ‖u‖ = 1 → G (-u) = -G u := by
    intro u hu
    simp only [G, phi_neg u hu, neg_neg, ← map_neg, neg_sub]
  set K := Metric.closedBall (0 : Fin d → ℝ) 1
  have hK : IsCompact K := isCompact_closedBall _ _
  obtain ⟨u0, _, hmin⟩ :=
    hK.exists_isMinOn ⟨0, by simp [K]⟩ (continuous_norm.comp hG).continuousOn
  set δ := ‖G u0‖
  have hδ : 0 < δ := norm_pos_iff.2 (hG0 u0)
  have hbig : ∀ u ∈ K, ∃ i, δ ≤ |G u i| := by
    intro u hu
    by_contra h
    push Not at h
    have h1 : ‖G u‖ < δ := (pi_norm_lt_iff hδ).2 (fun i => by
      simpa [Real.norm_eq_abs] using h i)
    have h2 : δ ≤ ‖G u‖ := hmin hu
    linarith
  obtain ⟨η, hη, hUC⟩ :=
    Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hG.continuousOn) δ hδ
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hη
  set m : ℕ := N + 1 with hm
  have hm0 : (0 : ℝ) < m := by positivity
  let U : (Fin d → ℤ) → (Fin d → ℝ) := fun x i => (x i : ℝ) / m
  have hUK : ∀ x : Fin d → ℤ, InBox m x → U x ∈ K := by
    intro x hx
    simp only [K, Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    have hxi : |(x i : ℝ)| ≤ m := by exact_mod_cast hx i
    simp only [U, Real.norm_eq_abs, abs_div, abs_of_pos hm0]
    exact (div_le_one hm0).2 hxi
  have hUneg : ∀ x : Fin d → ℤ, U (-x) = -U x := by
    intro x
    funext i
    simp [U, neg_div]
  have hUbd : ∀ x : Fin d → ℤ, InBox m x → (∃ a, |x a| = m) → ‖U x‖ = 1 := by
    intro x hx ⟨a, ha⟩
    refine le_antisymm ?_ ?_
    · simpa [K] using hUK x hx
    · have h1 := norm_le_pi_norm (U x) a
      have hxa : |(x a : ℝ)| = m := by exact_mod_cast ha
      have h2 : ‖U x a‖ = 1 := by
        simp only [U, Real.norm_eq_abs, abs_div, abs_of_pos hm0, hxa]
        exact div_self hm0.ne'
      linarith
  let lab : (Fin d → ℤ) → ℤ := fun x => labOf δ (G (U x))
  have hlab : ∀ x : Fin d → ℤ, InBox m x → lab x ≠ 0 ∧ |lab x| ≤ d := by
    intro x hx
    obtain ⟨i, hi, -⟩ := labOf_spec (G (U x)) (hbig _ (hUK x hx))
    have hid : (i : ℕ) + 1 ≤ d := i.isLt
    simp only [lab, hi]
    split_ifs
    · refine ⟨by omega, ?_⟩
      rw [one_mul, abs_of_nonneg (by omega)]
      exact_mod_cast hid
    · refine ⟨by omega, ?_⟩
      rw [neg_one_mul, abs_neg, abs_of_nonneg (by omega)]
      exact_mod_cast hid
  have hanti : ∀ x : Fin d → ℤ, InBox m x → (∃ a, |x a| = m) → lab (-x) = -lab x := by
    intro x hx hb
    simp only [lab, hUneg, hGneg _ (hUbd x hx hb), labOf_neg hδ]
  obtain ⟨x, y, hx, hy, hxy, hsum⟩ := tucker d m (by omega) lab hlab hanti
  have hdist : dist (U x) (U y) < η := by
    have : dist (U x) (U y) ≤ 1 / m := by
      refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
      have hxyi : |((x i : ℝ) - y i)| ≤ 1 := by exact_mod_cast hxy i
      simp only [U, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hm0]
      exact div_le_div_of_nonneg_right hxyi hm0.le
    have hN' : 1 / (m : ℝ) < η := by simpa [hm] using hN
    linarith
  have key : ∀ i, |G (U x) i - G (U y) i| < δ := by
    intro i
    have h1 := hUC (U x) (hUK x hx) (U y) (hUK y hy) hdist
    have h2 := dist_le_pi_dist (G (U x)) (G (U y)) i
    rw [Real.dist_eq] at h2
    linarith
  obtain ⟨i, hi, hix⟩ := labOf_spec (G (U x)) (hbig _ (hUK x hx))
  obtain ⟨j, hj, hjy⟩ := labOf_spec (G (U y)) (hbig _ (hUK y hy))
  simp only [lab, hi, hj] at hsum
  have hk := key i
  split_ifs at hsum with h1 h2 h2
  · omega
  · have hij : i = j := Fin.ext (by omega)
    subst hij
    rw [abs_of_pos h1] at hix
    rw [abs_of_nonpos (not_lt.1 h2)] at hjy
    rw [abs_lt] at hk
    linarith
  · have hij : i = j := Fin.ext (by omega)
    subst hij
    rw [abs_of_nonpos (not_lt.1 h1)] at hix
    rw [abs_of_pos h2] at hjy
    rw [abs_lt] at hk
    linarith
  · omega

end BorsukUlam.PartBU
end
end

section
noncomputable section
open Classical
namespace BorsukUlam
/-! ## Borsuk–Ulam -/
alias exists_eq_neg_dev := BorsukUlam.PartBU.exists_eq_neg_dev

end BorsukUlam
end
end

section
noncomputable section
open Classical
open BorsukUlam
theorem solution (d : ℕ)
    (f : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1, EuclideanSpace ℝ (Fin d))) :
    ∃ x, f x = f (-x) := by
  exact BorsukUlam.exists_eq_neg_dev d f
end
end
