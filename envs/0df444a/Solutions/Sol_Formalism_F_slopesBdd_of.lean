-- Prove2me | solution 1 for Formalism.F.slopesBdd_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:46:24.090806+00:00
-- url     : https://prove2.me/submissions/4cc69cfb-a601-480f-a142-a6cbad38b86b

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SlopesBdd
import Theorems.Thm_P2M_Formalism_F_linearIndependent_coe_basis__a76a956f08cf
import Theorems.Thm_Formalism_F_gram_intMatrix_eq_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
universe u
namespace Formalism.F
theorem _root_.solution (hG : GramDetLe.{u, 0, 0}) : SlopesBdd.{u} := by
  intro E _ _ _ L hL
  haveI := hL
  let e := Module.finBasis ℤ L
  have he : LinearIndependent ℝ (fun i => (e i : E)) := linearIndependent_coe_basis' L e

  let S : EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) →ₗ[ℝ] E :=
    { toFun := fun x => ∑ i, WithLp.ofLp x i • (e i : E)
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum, smul_smul] }
  have hSinj : LinearMap.ker S = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have h0 := Fintype.linearIndependent_iff.mp he (fun i => WithLp.ofLp x i) hx
    have h1 : WithLp.ofLp x = 0 := funext h0
    simpa using congrArg (WithLp.toLp 2) h1
  obtain ⟨K, hK0, hK⟩ := S.exists_antilipschitzWith hSinj
  have hKpos : (0 : ℝ) < K := hK0
  refine ⟨Real.log K, ?_⟩
  rintro t ⟨N, hNL, hN0, rfl⟩
  haveI hN : DiscreteTopology N := DiscreteTopology.of_subset (s := (L : Set E)) hL hNL
  let f := Module.finBasis ℤ N
  let M : Matrix (Fin (Module.finrank ℤ L)) (Fin (Module.finrank ℤ N)) ℤ :=
    fun i j => e.repr ⟨(f j : E), hNL (f j).2⟩ i
  have hfj : ∀ j, (f j : E) = ∑ i, (M i j : ℝ) • (e i : E) := by
    intro j
    have h := congrArg Subtype.val (e.sum_repr ⟨(f j : E), hNL (f j).2⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    simp only [M, Int.cast_smul_eq_zsmul]
    exact h.symm
  let w : Fin (Module.finrank ℤ N) → EuclideanSpace ℝ (Fin (Module.finrank ℤ L)) :=
    fun j => WithLp.toLp 2 (fun i => (M i j : ℝ))
  have hSw : ∀ j, S (w j) = (f j : E) := by
    intro j
    rw [hfj j]
    simp [S, w]
  have hcomp : ∀ c : Fin (Module.finrank ℤ N) → ℝ,
      ‖∑ j, c j • w j‖ ≤ (K : ℝ) * ‖∑ j, c j • (f j : E)‖ := by
    intro c
    have h1 : S (∑ j, c j • w j) = ∑ j, c j • (f j : E) := by
      simp only [map_sum, map_smul, hSw]
    rw [← h1]
    simpa [dist_eq_norm] using hK.le_mul_dist (∑ j, c j • w j) 0
  have hdet := hG E (EuclideanSpace ℝ (Fin (Module.finrank ℤ L))) (Fin (Module.finrank ℤ N))
    (fun j => (f j : E)) w K hcomp
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det, Fintype.card_fin] at hdet

  have hwli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h2 : ∑ j, c j • (f j : E) = 0 := by
      rw [← map_zero S, ← hc]
      simp only [map_sum, map_smul, hSw]
    exact Fintype.linearIndependent_iff.mp (linearIndependent_coe_basis' N f) c h2
  have hwpos : 0 < (Matrix.gram ℝ w).det := (Matrix.posDef_gram_of_linearIndependent hwli).det_pos
  rw [gram_intMatrix_eq_map M, ← RingHom.map_det] at hwpos
  have hd1 : (1 : ℝ) ≤ (Int.castRingHom ℝ) (M.transpose * M).det := by
    simp only [eq_intCast] at hwpos ⊢
    have : (0 : ℤ) < (M.transpose * M).det := by exact_mod_cast hwpos
    exact_mod_cast this
  have hk : (0 : ℝ) < (Module.finrank ℤ N : ℝ) := by
    haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.mpr hN0
    exact_mod_cast Module.finrank_pos
  set g := (Matrix.gram ℝ (fun j => (f j : E))).det with hg
  have hgK : 1 ≤ (K : ℝ) ^ (2 * Module.finrank ℤ N) * g := hd1.trans hdet
  have hgpos : 0 < g := by
    by_contra hneg
    push_neg at hneg
    have : (K : ℝ) ^ (2 * Module.finrank ℤ N) * g ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hlog : -(2 * (Module.finrank ℤ N : ℝ)) * Real.log K ≤ Real.log g := by
    have h1 : Real.log 1 ≤ Real.log ((K : ℝ) ^ (2 * Module.finrank ℤ N) * g) :=
      Real.log_le_log one_pos hgK
    rw [Real.log_one, Real.log_mul (by positivity) hgpos.ne', Real.log_pow] at h1
    push_cast at h1
    linarith
  have hcov : covol N = Real.sqrt g := by rw [covol, dif_pos hN]
  show -Real.log (covol N) / (Module.finrank ℤ N : ℝ) ≤ Real.log K
  rw [hcov, Real.log_sqrt hgpos.le, div_le_iff₀ hk]
  nlinarith
end Formalism.F
