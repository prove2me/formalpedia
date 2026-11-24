-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.exists_node
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:40.035627+00:00
-- url     : https://prove2.me/submissions/e9c83d55-260f-4588-b3ce-78d1b6a6c13f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Node_div_mem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Node_exists_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Node_pol_eval
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Node_pol_natDegree_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_adjugate
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution [CharZero K] (hS : IsLocUnif S ϖ) (n : Type*) [Fintype n] [DecidableEq n] :
    ∃ l : ℕ, ∀ X : Matrix n n K, Ent S X → X.det ≠ 0 → X.det⁻¹ ∈ S →
      ∃ c ∈ S, c + star c = 1 ∧ ∃ W' : Matrix n n K, Ent S W' ∧
        (c • (1 : Matrix n n K) + star c • X) * W' = ϖ ^ l • (1 : Matrix n n K) := by
  obtain ⟨τ, hτS, hτ⟩ := hS.tr
  obtain ⟨θ, hθS, hθs, hθ0⟩ := hS.skew
  have hdetS : ∀ M : Matrix n n K, Ent S M → M.det ∈ S := by
    intro M hM
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_det]
    exact SetLike.coe_mem _
  have hadjS : ∀ M : Matrix n n K, Ent S M → Ent S M.adjugate := by
    intro M hM i j
    have e : M = S.subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : S)) := by
      ext i j; rfl
    rw [e, ← RingHom.map_adjugate]
    exact SetLike.coe_mem _
  have hnot : ϖ⁻¹ ∉ S := by
    intro h
    have := (hS.rad (-ϖ⁻¹) (S.neg_mem h)).1
    apply this
    rw [mul_neg, mul_inv_cancel₀ hS.ne]
    ring
  let N := Fintype.card n
  let s : Finset ℕ := Finset.range (2 * N + 1)
  let v : ℕ → K := fun k => τ + (k : K) * θ
  have hv : Set.InjOn v s := by
    intro a _ b _ hab
    have h1 : (a : K) * θ = (b : K) * θ := add_left_cancel hab
    exact_mod_cast mul_right_cancel₀ hθ0 h1
  have hvS : ∀ k, v k ∈ S := fun k => S.add_mem hτS (S.mul_mem (natCast_mem S k) hθS)
  have hvs : ∀ k, star (v k) = 1 - v k := by
    intro k
    simp only [v, star_add, star_mul', star_natCast, hθs]
    linear_combination hτ
  obtain ⟨l, hl⟩ := Node.exists_pow hS s (fun k => (Lagrange.basis s v k).eval 1)
  refine ⟨l, fun X hX hd hdi => ?_⟩
  let R : K[X] := Node.pol (1 - X) X * Node.pol (Xᴴ - 1) 1
  have hRdeg : R.degree < (s.card : WithBot ℕ) := by
    have h1 : R.natDegree ≤ 2 * N := by
      refine (Polynomial.natDegree_mul_le).trans ?_
      rw [two_mul]
      exact add_le_add (Node.pol_natDegree_le _ _) (Node.pol_natDegree_le _ _)
    refine lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le h1) ?_
    simp only [s, Finset.card_range]
    exact_mod_cast Nat.lt_succ_self _
  have hReval : ∀ c : K, star c = 1 - c →
      R.eval c = (c • (1 : Matrix n n K) + star c • X).det *
        star ((c • (1 : Matrix n n K) + star c • X).det) := by
    intro c hc
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval, ← Matrix.det_conjTranspose]
    congr 2
    · rw [hc, smul_sub, sub_smul, one_smul]; abel
    · simp only [conjTranspose_add, conjTranspose_smul, conjTranspose_one, star_star]
      rw [hc, smul_sub, sub_smul, one_smul]; abel
  have hR1 : R.eval 1 = star X.det := by
    simp only [R]
    rw [Polynomial.eval_mul, Node.pol_eval, Node.pol_eval]
    simp [Matrix.det_conjTranspose]
  have hsum : R.eval 1 = ∑ k ∈ s, R.eval (v k) * (Lagrange.basis s v k).eval 1 := by
    conv_lhs => rw [Lagrange.eq_interpolate hv hRdeg]
    rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  have hX0 : X.det ≠ 0 := hd
  have hR1S : (R.eval 1)⁻¹ ∈ S := by
    rw [hR1, ← star_inv₀]
    exact hS.star_mem _ hdi
  have hR10 : R.eval 1 ≠ 0 := by
    rw [hR1]; exact star_ne_zero.mpr hX0
  have hMS : ∀ k, Ent S (v k • (1 : Matrix n n K) + star (v k) • X) := by
    intro k i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    refine S.add_mem (S.mul_mem (hvS k) ?_) (S.mul_mem (hS.star_mem _ (hvS k)) (hX i j))
    split_ifs
    · exact S.one_mem
    · exact S.zero_mem
  have hex : ∃ k ∈ s, R.eval (v k) * (ϖ⁻¹) ^ (l + 1) ∉ S := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    have h1 : R.eval 1 * ϖ⁻¹ ∈ S := by
      have e : R.eval 1 * ϖ⁻¹ =
          ∑ k ∈ s, (R.eval (v k) * (ϖ⁻¹) ^ (l + 1)) * (ϖ ^ l * (Lagrange.basis s v k).eval 1) := by
        rw [hsum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        have e1 : ϖ ^ l * (ϖ⁻¹) ^ (l + 1) = ϖ⁻¹ := by
          rw [pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hS.ne, one_pow, one_mul]
        linear_combination (-(Polynomial.eval (v k) R * Polynomial.eval 1 (Lagrange.basis s v k))) * e1
      rw [e]
      exact S.sum_mem fun k hk => S.mul_mem (hcon k hk) (hl k hk)
    have e2 : ϖ⁻¹ = (R.eval 1)⁻¹ * (R.eval 1 * ϖ⁻¹) := by
      field_simp
    rw [e2]
    exact S.mul_mem hR1S h1
  obtain ⟨k, hk, hkn⟩ := hex
  set M := v k • (1 : Matrix n n K) + star (v k) • X with hMdef
  have hfk : R.eval (v k) = M.det * star M.det := hReval (v k) (hvs k)
  have hfS : R.eval (v k) ∈ S := by
    rw [hfk]; exact S.mul_mem (hdetS M (hMS k)) (hS.star_mem _ (hdetS M (hMS k)))
  have hfs : star (R.eval (v k)) = R.eval (v k) := by
    rw [hfk, star_mul', star_star, mul_comm]
  have hf0 : R.eval (v k) ≠ 0 := by
    intro h0; apply hkn; rw [h0, zero_mul]; exact S.zero_mem
  have hdiv := Node.div_mem hS l _ hfS hfs hkn
  have hM0 : M.det ≠ 0 := by
    intro h0; apply hf0; rw [hfk, h0, zero_mul]
  have hcS : ϖ ^ l * M.det⁻¹ ∈ S := by
    have e : ϖ ^ l * M.det⁻¹ = ϖ ^ l * (R.eval (v k))⁻¹ * star M.det := by
      rw [hfk]
      have : star M.det ≠ 0 := star_ne_zero.mpr hM0
      field_simp
    rw [e]
    exact S.mul_mem hdiv (hS.star_mem _ (hdetS M (hMS k)))
  refine ⟨v k, hvS k, by rw [hvs k]; ring, (ϖ ^ l * M.det⁻¹) • M.adjugate, ?_, ?_⟩
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact S.mul_mem hcS (hadjS M (hMS k) i j)
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    congr 1
    rw [← hMdef]
    field_simp
end Formalism.HermitianLattices.Ext.L3.HU
