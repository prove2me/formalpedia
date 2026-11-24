-- Prove2me | solution 1 for BSLambda.LLL.mem_flagEvent_of_intObstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:29:30.864922+00:00
-- url     : https://prove2.me/submissions/e38aed19-126a-4839-88cd-d63e217fb58f

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_mem_flagEvent
public import Theorems.Thm_BSLambda_LLL_exists_active_flag_of_intObstruction

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool}
    (hT : IsTournament Arc)
    {ω : GateCfg ι r} {S : Finset ι} (hS : S.card = 5) {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h (toGamma ω)) :
    ∃ F : Flag1 ι, F.Active Arc ∧ F.supp = S ∧ ω ∈ flagEvent Arc F := by
  obtain ⟨F, hact, hsupp, hFh, hgate⟩ :=
    exists_active_flag_of_intObstruction hT hS hh hobs
  refine ⟨F, hact, hsupp, mem_flagEvent.2 fun p hp ↦ ?_⟩
  rw [hFh]
  exact hgate p hp
end BSLambda.LLL
