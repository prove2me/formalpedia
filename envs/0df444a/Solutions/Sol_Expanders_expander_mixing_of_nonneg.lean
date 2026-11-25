-- Prove2me | solution 1 for Expanders.expander_mixing_of_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T15:43:29.918034+00:00
-- url     : https://prove2.me/submissions/d4c399d3-24f4-49d0-865e-8eaea1f7e1f5

module
public import Mathlib
public import Definitions.Def_ExpanderLib_MixingAux
public import Definitions.Def_ExpanderLib_NilliBall
public import Definitions.Def_ExpanderLib_Expanders
public import Theorems.Thm_Expanders_abs_dotProduct_adjMatrix_le
public import Theorems.Thm_Expanders_adjMatrix_dotProduct_comm


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix
open Expanders
variable {V : Type*} [Fintype V]
namespace Expanders
theorem _root_.solution (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) {μ : ℝ} (hμ0 : 0 ≤ μ)
    (hμ : ∀ x : V → ℝ, ∑ v, x v = 0 → |dotProduct x (G.adjMatrix ℝ *ᵥ x)| ≤ μ * dotProduct x x)
    (S T : Finset V) :
    |(edgeCount G S T : ℝ) - d * S.card * T.card / Fintype.card V| ≤
      μ * Real.sqrt (S.card * T.card) := by
  classical
  set n := Fintype.card V with hn
  by_cases hn0 : n = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn0
    rw [Finset.eq_empty_of_isEmpty S, Finset.eq_empty_of_isEmpty T]
    simp [edgeCount]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  set A := G.adjMatrix ℝ
  set iS : V → ℝ := fun v => if v ∈ S then 1 else 0 with hiS
  set iT : V → ℝ := fun v => if v ∈ T then 1 else 0 with hiT
  -- the edge count as a bilinear form
  have hE : (edgeCount G S T : ℝ) = dotProduct iS (A *ᵥ iT) := by
    rw [edgeCount, Finset.card_filter, Finset.sum_product]
    push_cast
    simp only [hiS, hiT, A, dotProduct, mulVec, adjMatrix_apply, ite_mul, one_mul, zero_mul,
      mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hA1 : A *ᵥ (1 : V → ℝ) = (d : ℝ) • 1 := by
    funext v
    simp [A, adjMatrix_mulVec_apply, card_neighborFinset_eq_degree, hd v]
  have hind1 : ∀ U : Finset V, dotProduct (fun v => if v ∈ U then (1 : ℝ) else 0) 1 = U.card := by
    intro U; simp [dotProduct_one]
  have hind2 : ∀ U : Finset V, dotProduct (fun v => if v ∈ U then (1 : ℝ) else 0)
      (fun v => if v ∈ U then (1 : ℝ) else 0) = U.card := by
    intro U; simp [dotProduct]
  have h11 : dotProduct (1 : V → ℝ) 1 = n := by simp [dotProduct, hn]
  have hS1 : dotProduct iS 1 = S.card := hind1 S
  have hT1' : dotProduct iT 1 = T.card := hind1 T
  have hSS : dotProduct iS iS = S.card := hind2 S
  have hTT : dotProduct iT iT = T.card := hind2 T
  set a : ℝ := S.card / n with ha
  set b : ℝ := T.card / n with hb
  set x : V → ℝ := iS - a • 1 with hx
  set y : V → ℝ := iT - b • 1 with hy
  have hxs : ∑ v, x v = 0 := by
    have : ∑ v, x v = dotProduct x 1 := by rw [dotProduct_one]
    rw [this, hx, sub_dotProduct, smul_dotProduct, hind1, h11, smul_eq_mul, ha]
    field_simp; ring
  have hys : ∑ v, y v = 0 := by
    have : ∑ v, y v = dotProduct y 1 := by rw [dotProduct_one]
    rw [this, hy, sub_dotProduct, smul_dotProduct, hind1, h11, smul_eq_mul, hb]
    field_simp; ring
  -- the bilinear term
  have hxy : dotProduct x (A *ᵥ y) =
      (edgeCount G S T : ℝ) - d * S.card * T.card / n := by
    have hT1 : dotProduct (1 : V → ℝ) (A *ᵥ iT) = d * T.card := by
      rw [adjMatrix_dotProduct_comm, hA1, dotProduct_smul, hT1', smul_eq_mul]
    rw [hE, hx, hy, mulVec_sub, mulVec_smul, hA1]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      hS1, h11, hT1]
    rw [ha, hb]
    field_simp
    ring
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have han : a * n = S.card := by rw [ha]; field_simp
  have hbn : b * n = T.card := by rw [hb]; field_simp
  have hxx : dotProduct x x ≤ S.card := by
    rw [hx]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      hS1, hSS, h11, dotProduct_comm (1 : V → ℝ) iS]
    have h2 : a * (a * n) = a * S.card := by rw [han]
    nlinarith [mul_nonneg ha0 (Nat.cast_nonneg (α := ℝ) S.card)]
  have hyy : dotProduct y y ≤ T.card := by
    rw [hy]
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      hT1', hTT, h11, dotProduct_comm (1 : V → ℝ) iT]
    have h2 : b * (b * n) = b * T.card := by rw [hbn]
    nlinarith [mul_nonneg hb0 (Nat.cast_nonneg (α := ℝ) T.card)]
  rw [← hxy]
  refine (abs_dotProduct_adjMatrix_le G hμ x y hxs hys).trans ?_
  apply mul_le_mul_of_nonneg_left _ hμ0
  rw [Real.sqrt_mul (Nat.cast_nonneg _)]
  exact mul_le_mul (Real.sqrt_le_sqrt hxx) (Real.sqrt_le_sqrt hyy) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)
end Expanders
