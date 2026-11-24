-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.pc_mem_Dpcris
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:54:08.543805+00:00
-- url     : https://prove2.me/submissions/ccae7491-b7e7-427f-a565-e936b0437b6d

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_DpcrisStable
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_DPotCrisStableAndExistsPotentiallyCrystallineDat
import Theorems.Thm_Formalism_WeaklyAdmissibleFiltrations_pc_actVB_res

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution {x : V ⊗[Qp] B} :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ (h : G) x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, pc_actVB_res]
end Formalism.WeaklyAdmissibleFiltrations
