-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.Step.tendsto_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:46:35.599071+00:00
-- url     : https://prove2.me/submissions/57f42d05-b9b7-4d2a-8879-7cb6ded9faad

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepMassEqProdPsi
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoBallCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSingSSum
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassRatioEqLvalue
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LamGEqOneOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FactorIdentity
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassConstSucc
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallSum_integral_of_mem_genus
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_integral_of_mem_genus
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_mass_eq_sum
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integral_of_mem_genus
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_tendsto_ballCount


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
open Formalism.HermitianLattices.Ext.L3.Step
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.Step
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Tendsto (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (Formalism.HermitianLatticesTheory.mass h L *
        ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
          (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L)))) := by
  rw [RankOne.mass_eq_sum h L s hsr, Finset.sum_mul]
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun M hM => ?_
  have hg := hsr.1 M hM
  obtain ⟨hMi, -, hMD⟩ := integral_of_mem_genus hK hF hs hd hL hLi hg
  have ht := (tendsto_ballCount hK hF hs hd hg.1 hMi).const_mul
    ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)⁻¹)
  rw [hMD] at ht
  refine ht.congr fun j => ?_
  rw [div_eq_mul_inv (ballCount h M ((j : ℝ) ^ 2) : ℝ), div_eq_mul_inv, div_eq_mul_inv]
  ring
end Formalism.HermitianLattices.Ext.L3.Step
