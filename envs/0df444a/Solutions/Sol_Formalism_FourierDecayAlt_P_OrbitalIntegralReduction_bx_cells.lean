-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_cells
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:09.643122+00:00
-- url     : https://prove2.me/submissions/30dcd38c-fb42-4376-ab61-0dade013cfe5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_cells
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_bx_eq_S
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_lat_pi
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_good_equiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_good_fin
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_lat_map
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mem_LL
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] [DecidableEq ι] {Q : Type}
    (c : Q → ι → K) (M : Q → Matrix ι ι K) (hM : ∀ q, IsUnit (M q).det)
    (hpart : ∀ v : ι → K, ∃! q, ∃ r : ι → K, (∀ i, r i ∈ R) ∧ v = c q + M q *ᵥ r)
    (f : (ι → K) → ℂ) (hf : ∀ q (r : ι → K), (∀ i, r i ∈ R) → f (c q + M q *ᵥ r) = f (c q))
    (hfin : {q | f (c q) ≠ 0}.Finite) {Λ : AddSubgroup K} (hΛ : IsLat Λ) (hinv : BInv Λ f) :
    bx R Λ ι f = ∑ᶠ q, (modK R (M q).det : ℂ) * f (c q) := by
  have hL : Lat (LL R ι) := lat_LL hD.isOpen hD.isCompact
  have hG : Good R ι := good_equiv (Fintype.equivFin ι).symm (good_fin hD _)
  have hmem : ∀ q (v : ι → K), v - c q ∈ (LL R ι).map (mv (M q)) ↔
      ∃ r : ι → K, (∀ i, r i ∈ R) ∧ v = c q + M q *ᵥ r := by
    intro q v
    constructor
    · rintro ⟨r, hr, e⟩
      refine ⟨r, mem_LL.1 hr, ?_⟩
      rw [mv_apply] at e
      rw [e]; abel
    · rintro ⟨r, hr, e⟩
      refine ⟨r, mem_LL.2 hr, ?_⟩
      rw [mv_apply, e]; abel
  rw [tk_bx_eq_S R Λ f hinv, tk_cells hL c (fun q => (LL R ι).map (mv (M q)))
    (fun q => lat_map (hM q) hL) ?_ f ?_ hfin (tk_lat_pi hΛ) ?_]
  · refine finsum_congr fun q => ?_
    rw [← hG (M q) (hM q)]
    rfl
  · intro v
    obtain ⟨q, hq, hu⟩ := hpart v
    exact ⟨q, (hmem q v).2 hq, fun q' hq' => hu q' ((hmem q' v).1 hq')⟩
  · rintro q _ ⟨r, hr, rfl⟩
    exact hf q r (mem_LL.1 hr)
  · intro v l hl
    exact hinv v l (fun i => by
      have := (AddSubgroup.mem_pi _).1 hl i (Set.mem_univ i)
      exact this)
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
