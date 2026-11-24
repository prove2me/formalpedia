-- Prove2me | solution 1 for BSLambda.LLL.intObstruction_one_gate_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:30.667801+00:00
-- url     : https://prove2.me/submissions/bf03b93e-e447-42e5-b14a-3fe6649f4791

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_intObstruction_one_of_owner_arc
public import Theorems.Thm_BSLambda_LLL_intObstruction_one_of_arc_to_owner
public import Theorems.Thm_BSLambda_IsTournament_arc_of_not_arc


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace BSLambda.LLL
theorem _root_.solution {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hih : i ≠ h) (hjh : j ≠ h) (harc : Arc i j = true) (hhj : Arc h j = true) :
    γ i j = γ h j := by
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  obtain ⟨hZj, -⟩ := intObstruction_one_of_owner_arc hgate hbud hj hjh hhj
  have hmem : γ i j ∈ Z j := by
    cases hhi : Arc h i with
    | true => exact (intObstruction_one_of_owner_arc hgate hbud hi hih hhi).2 j hj harc
    | false =>
      exact (intObstruction_one_of_arc_to_owner hh hZh hbud hi hih
        (hT.arc_of_not_arc hih hhi)).2 j hj hjh harc
  rwa [hZj, Finset.mem_singleton] at hmem
end BSLambda.LLL
