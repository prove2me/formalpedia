-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.op_prod_shape
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:56.04356+00:00
-- url     : https://prove2.me/submissions/6326aa52-f2d7-4306-817d-181742b721b0

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementI
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowDeg_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_rowDeg_add
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_op_minorProd_shape
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_prod_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_shape_prod_le
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds MvPolynomial
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {K : Type u} [Field K] {d N0 N1 : ℕ} [NeZero d] (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) (colN : ZMod d → ℕ) (p : ∀ s, Fin (colN s) → ℕ)
    (hp : ∀ s c, p s c ≤ N0) (hp1 : ∀ s c, 1 ≤ p s c) (I : ∀ s c, Fin (p s c) → Fin N1)
    (κ : ZV d N0 N1 →₀ ℕ)
    (hκ : κ ∈ (∏ s : ZMod d, minorProd (rowOp (N1 := N1) TT T s) (p s) (hp s) (I s)).support)
    (s : ZMod d) :
    (∑ k, rowDeg s k κ) = ∑ c, p s c ∧ (∀ k, rowDeg s k κ ≤ colN s) ∧
      (s ∈ TT → ∀ k0 : Fin N0, k0.val = 0 → rowDeg s k0 κ = colN s ∧
        ∀ k : Fin N0, k.val ≠ 0 →
          rowDeg s k κ ≤ (Finset.univ.filter (fun c => 2 ≤ p s c)).card) := by
  classical
  have hG := fun s' => op_minorProd_shape TT T s' (p s') (hp s') (I s')
  refine ⟨?_, fun k => ?_, fun hs k0 hk0 => ⟨?_, fun k hk => ?_⟩⟩
  · have := shape_prod_eq (R := K) (fun m => ∑ k, rowDeg s k m) (by simp [rowDeg_zero])
      (fun a b => by simp [rowDeg_add, Finset.sum_add_distrib]) _
      (fun s' => if s' = s then ∑ c, p s' c else 0) Finset.univ
      (fun s' _ m hm => by
        by_cases h : s' = s
        · subst h
          rw [if_pos rfl]
          exact (hG s' m hm).2.1
        · rw [if_neg h]
          exact Finset.sum_eq_zero fun k _ => (hG s' m hm).1 s k (Ne.symm h)) κ hκ
    simpa using this
  · have := shape_prod_le (R := K) (rowDeg s k) (rowDeg_zero _ _) (rowDeg_add _ _) _
      (fun s' => if s' = s then colN s' else 0) Finset.univ
      (fun s' _ m hm => by
        by_cases h : s' = s
        · subst h
          rw [if_pos rfl]
          exact (hG s' m hm).2.2.1 k
        · rw [if_neg h]
          exact le_of_eq ((hG s' m hm).1 s k (Ne.symm h))) κ hκ
    simpa using this
  · have := shape_prod_eq (R := K) (rowDeg s k0) (rowDeg_zero _ _) (rowDeg_add _ _) _
      (fun s' => if s' = s then colN s' else 0) Finset.univ
      (fun s' _ m hm => by
        by_cases h : s' = s
        · subst h
          rw [if_pos rfl]
          exact ((hG s' m hm).2.2.2 hs (hp1 s') k0 hk0).1
        · rw [if_neg h]
          exact (hG s' m hm).1 s k0 (Ne.symm h)) κ hκ
    simpa using this
  · have := shape_prod_le (R := K) (rowDeg s k) (rowDeg_zero _ _) (rowDeg_add _ _) _
      (fun s' => if s' = s then (Finset.univ.filter (fun c => 2 ≤ p s' c)).card else 0) Finset.univ
      (fun s' _ m hm => by
        by_cases h : s' = s
        · subst h
          rw [if_pos rfl]
          exact ((hG s' m hm).2.2.2 hs (hp1 s') k0 hk0).2 k hk
        · rw [if_neg h]
          exact le_of_eq ((hG s' m hm).1 s k (Ne.symm h))) κ hκ
    simpa using this
end Formalism.DworkPowerSeriesWeights
