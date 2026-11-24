-- Prove2me | solution 1 for BSLambda.LLL.intObstruction_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:26:12.067125+00:00
-- url     : https://prove2.me/submissions/9c0a5376-cf79-4925-8733-95fd87c4a69a

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_missSet_congr
public import Theorems.Thm_BSLambda_IsTournament_ne_of_arc


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
    {ell : ℕ} {S : Finset ι} {h : ι} (hh : h ∈ S) {γ γ' : ι → ι → Fin r}
    (hagree : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → γ a b = γ' a b)
    (hobs : IntObstruction Arc ell S h γ) : IntObstruction Arc ell S h γ' := by
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  refine ⟨Z, hZh, fun j hj harc ↦ ?_, fun i hi hin ↦ ?_⟩
  · rw [← hagree h hh j hj (hT.ne_of_arc harc)]
    exact hgate j hj harc
  · rw [← missSet_congr hT hi Z hagree]
    exact hbud i hi hin
end BSLambda.LLL
