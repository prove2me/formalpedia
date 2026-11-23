-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.bx_lin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:32.275061+00:00
-- url     : https://prove2.me/submissions/e1856ff6-4f8f-4c84-af3b-e3e5c1e52a5f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Bd_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_Sm_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_fin_cpt
import Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_bx_cells
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
theorem _root_.solution (hD : LocalDatum K R ψ) {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι K)
    (hM : IsUnit M.det) (b : ι → K) {Λ L : AddSubgroup K} (hΛ : IsLat Λ) (hL : IsLat L)
    (f : (ι → K) → ℂ) (hinv : BInv Λ f) (hs : BSupp L f)
    (hR : ∀ ξ r : ι → K, (∀ i, r i ∈ R) → f (M *ᵥ (ξ + r) + b) = f (M *ᵥ ξ + b)) :
    bx R Λ ι f = (modK R M.det : ℂ) *
      ∑ᶠ q : ι → KR R, f (M *ᵥ (fun i => Quotient.out (q i)) + b) := by
  have hmk : ∀ z : KR R, (Submodule.Quotient.mk (Quotient.out z : K) : KR R) = z :=
    fun z => Quotient.out_eq z
  have hMi : ∀ w : ι → K, M⁻¹ *ᵥ (M *ᵥ w) = w := by
    intro w; rw [mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec]
  have hiM : ∀ w : ι → K, M *ᵥ (M⁻¹ *ᵥ w) = w := by
    intro w; rw [mulVec_mulVec, mul_nonsing_inv _ hM, one_mulVec]
  rw [bx_cells hD (fun q : ι → KR R => M *ᵥ (fun i => (Quotient.out (q i) : K)) + b) (fun _ => M)
    (fun _ => hM) ?_ f ?_ ?_ hΛ hinv, mul_finsum]
  · intro v
    refine ⟨fun i => Submodule.Quotient.mk ((M⁻¹ *ᵥ (v - b)) i), ⟨fun i => (M⁻¹ *ᵥ (v - b)) i -
      (Quotient.out (Submodule.Quotient.mk ((M⁻¹ *ᵥ (v - b)) i) : KR R) : K), ?_, ?_⟩, ?_⟩
    · intro i
      exact (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).1 (hmk _).symm
    · have key : ∀ w o : ι → K, w = M⁻¹ *ᵥ (v - b) →
          v = M *ᵥ o + b + M *ᵥ (fun i => w i - o i) := by
        intro w o hw
        have e : o + (fun i => w i - o i) = w := by funext i; simp
        calc v = M *ᵥ w + b := by rw [hw, hiM]; abel
          _ = M *ᵥ (o + fun i => w i - o i) + b := by rw [e]
          _ = M *ᵥ o + b + M *ᵥ (fun i => w i - o i) := by rw [mulVec_add]; abel
      exact key _ _ rfl
    · rintro q ⟨r, hr, e⟩
      funext i
      have e3 : M⁻¹ *ᵥ (v - b) = (fun i => (Quotient.out (q i) : K)) + r := by
        rw [e]
        have : M *ᵥ (fun i => (Quotient.out (q i) : K)) + b + M *ᵥ r - b =
            M *ᵥ ((fun i => (Quotient.out (q i) : K)) + r) := by
          rw [mulVec_add]; abel
        rw [this, hMi]
      rw [e3, ← hmk (q i)]
      refine (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).2 ?_
      simpa using R.neg_mem (hr i)
  · intro q r hr
    have := hR (fun i => (Quotient.out (q i) : K)) r hr
    rw [← this, mulVec_add]
    congr 1
    abel
  · have hB : IsCompact (Set.pi Set.univ (fun _ : ι => (L : Set K))) :=
      isCompact_univ_pi (fun _ => hL.2)
    have hT : Continuous fun x : ι → K => M⁻¹ *ᵥ (x - b) :=
      Continuous.matrix_mulVec continuous_const (continuous_id.sub continuous_const)
    have hC : ∀ i, IsCompact ((fun x : ι → K => x i) ''
        ((fun x : ι → K => M⁻¹ *ᵥ (x - b)) '' Set.pi Set.univ (fun _ : ι => (L : Set K)))) :=
      fun i => (hB.image hT).image (continuous_apply i)
    have h1 : ∀ i, {z : KR R | (Quotient.out z : K) ∈ (fun x : ι → K => x i) ''
        ((fun x : ι → K => M⁻¹ *ᵥ (x - b)) '' Set.pi Set.univ (fun _ : ι => (L : Set K)))}.Finite :=
      fun i => tk_fin_cpt R.toAddSubgroup hD.isOpen (fun z : KR R => (Quotient.out z : K))
        (fun q q' h => by
          have := (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).2 h
          rwa [hmk, hmk] at this)
        (fun y => ⟨Submodule.Quotient.mk y, (Formalism.FourierDecayAlt.P.A5x3.mk_eq_mk R _ _).1 (hmk _).symm⟩) (hC i)
    refine (Set.Finite.pi' h1).subset ?_
    intro q hq i
    refine ⟨M⁻¹ *ᵥ (M *ᵥ (fun i => (Quotient.out (q i) : K)) + b - b),
      ⟨M *ᵥ (fun i => (Quotient.out (q i) : K)) + b, Set.mem_univ_pi.2 (hs _ hq), rfl⟩, ?_⟩
    show (M⁻¹ *ᵥ (M *ᵥ (fun i => (Quotient.out (q i) : K)) + b - b)) i = _
    rw [add_sub_cancel_right, hMi]
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
