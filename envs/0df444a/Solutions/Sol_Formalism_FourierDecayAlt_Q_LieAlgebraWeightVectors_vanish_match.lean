-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.vanish_match
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:50:48.980424+00:00
-- url     : https://prove2.me/submissions/1edb3068-7ff2-41d6-964b-7edd05db7227

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_Vanish
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_Pq_OK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
private theorem linearMap_coeAddMonoidHom_eq_mapRange_smul {ι : Type*} [DecidableEq ι] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (S : ι → Submodule ℂ W) (L : W →ₗ[ℂ] W) (a : ι → ℂ) (hL : ∀ i, ∀ y ∈ S i, L y = a i • y)
    (f : DirectSum ι (fun i => S i)) :
    L (DirectSum.coeAddMonoidHom S f) = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange.addMonoidHom (fun i => DistribSMul.toAddMonoidHom (S i) (a i)) f) := by
  induction f using DirectSum.induction_on with
  | zero => simp
  | of i y =>
    rw [DirectSum.coeAddMonoidHom_of, hL i y y.2]
    change _ = DirectSum.coeAddMonoidHom S
      (DFinsupp.mapRange _ (fun j => map_zero _) (DFinsupp.single (β := fun j => S j) i y))
    rw [DFinsupp.mapRange_single]
    change _ = DirectSum.coeAddMonoidHom S (DirectSum.of (fun j => S j) i _)
    rw [DirectSum.coeAddMonoidHom_of]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
end
end

set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
theorem _root_.solution (hBr : Branching) {P : M.Par} (hP : P.OK) {Wp : Type} [NormedAddCommGroup Wp]
    [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    (hz : inWb P.k P.r z) (hT : 0 < Tz P.k P.r z) (hπ : IsType P.k P.r z π P.u)
    {e : Fin (2 * P.r + P.k + 1) → ℂ} (he : inWb P.k P.r e) (hez : herm (Hpk P.k P.r) e z = 0)
    (hee : herm (Hpk P.k P.r) e e = 1) (Bs : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (hBs : IsFrameOf P.k P.r [z, e] Bs) (hlin : ∀ w : ℂ, IsLinearMap ℂ (capRep P.k P.r π Bs w))
    {x : Wp} (hx : x ≠ 0) (μ : ℂ → ℂ) (hμ : ∀ w : ℂ, capRep P.k P.r π Bs w x = μ (w - ((P.k : ℂ) - 2) / 2) • x) :
    ∃ ρ : M.Ty (Pq P), ∀ Y : ℂ, μ Y = M.xC (Pq P) ρ Y := by
  obtain ⟨S, hS, -, hcap⟩ := hBr Wp (Pq P) (Pq_OK hP) rfl z e π hz hT hπ he hez hee
  obtain ⟨d, hd⟩ := hS.2 x
  obtain ⟨ρ, hρ⟩ : ∃ ρ, d ρ ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by rw [← hd, show d = 0 from DFinsupp.ext h, map_zero])
  refine ⟨ρ, fun Y => ?_⟩
  have hw : Y + ((P.k : ℂ) - 2) / 2 - ((P.k : ℂ) - 2) / 2 = Y := add_sub_cancel_right _ _
  have h1 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (IsLinearMap.mk' _ (hlin (Y + ((P.k : ℂ) - 2) / 2)))
    (fun σ => M.xC (Pq P) σ Y)
    (fun σ y hy => (hcap Bs hBs σ _ y hy).trans (congrArg (fun t => M.xC (Pq P) σ t • y) hw)) d
  have h2 := linearMap_coeAddMonoidHom_eq_mapRange_smul S (μ Y • LinearMap.id) (fun _ => μ Y) (fun _ _ _ => rfl) d
  have h3 : (DFinsupp.mapRange.addMonoidHom fun i =>
        DistribSMul.toAddMonoidHom (S i) (M.xC (Pq P) i Y)) d =
      (DFinsupp.mapRange.addMonoidHom fun i => DistribSMul.toAddMonoidHom (S i) (μ Y)) d :=
    hS.1 (by
      rw [← h1, ← h2, hd]
      simpa [hw] using hμ (Y + ((P.k : ℂ) - 2) / 2))
  have h4 := congrArg (fun f => f ρ) h3
  simp only [DFinsupp.mapRange.addMonoidHom_apply, DFinsupp.mapRange_apply,
    DistribSMul.toAddMonoidHom_apply] at h4
  exact (smul_left_injective ℂ hρ h4).symm
end Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
