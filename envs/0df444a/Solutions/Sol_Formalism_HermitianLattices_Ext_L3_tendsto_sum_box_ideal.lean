-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.tendsto_sum_box_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:34:51.67444+00:00
-- url     : https://prove2.me/submissions/67071bb2-7031-400e-b168-20ec9e148954

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoMeanAlphaN
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_BoxInterEqEmpty
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumOfMean
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumBoxIdeal
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_exists_abs_alphaN_le
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_tendsto_sum_of_mean
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_alphaN_congr
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_tendsto_mean_alphaN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Filter Topology
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S) {b : Ideal (𝓞 F)} (hb : b ≠ ⊥)
    (hbS : ∀ 𝔭 ∈ S, b ⊔ 𝔭.1 = ⊤) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n ∈ b},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) *
            ∏ 𝔭 ∈ S, alphaN h L 𝔭.1 n / (1 - etaF K F 𝔭.1 ^ finrank K V *
              (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ))))
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm b : ℝ) *
          ∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)) := by
  choose C hC using fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} =>
    exists_abs_alphaN_le hK hF hs hd hL hLi hm 𝔭.2
  have key := BoxSum.tendsto_sum_of_mean hK hF (m := finrank K V) (by omega) S
    (fun 𝔭 n => alphaN h L 𝔭.1 n) C (fun 𝔭 => 2 * vd h L 𝔭.1 + 2) (fun 𝔭 _ n => hC 𝔭 n)
    (fun 𝔭 _ n n' k hn hk hc => alphaN_congr hK hF hs hd hL hLi 𝔭.2 hn (by omega) hc)
    (fun 𝔭 _ => tendsto_mean_alphaN hK hF hs hd hL hLi hm 𝔭.2) hb hbS
  refine (key.mul_const (∏ 𝔭 ∈ S, (1 - etaF K F 𝔭.1 ^ finrank K V *
            (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))⁻¹)).congr fun j => ?_
  rw [mul_assoc, finsum_mem_mul]
  congr 1
  refine finsum_mem_congr rfl fun n _ => ?_
  simp only [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, mul_assoc]
end Formalism.HermitianLattices.Ext.L3
