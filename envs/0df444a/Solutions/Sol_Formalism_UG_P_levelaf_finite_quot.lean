-- Prove2me | solution 1 for Formalism.UG.P.levelaf_finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:22:44.707542+00:00
-- url     : https://prove2.me/submissions/3d8dd0a2-91b6-4acd-8e6a-3103a2e34853

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_adele_res
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem
import Theorems.Thm_Formalism_UG_P_levelaf_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution (D : 𝓞 F) (hD : D ≠ 0) (c : 𝒮) (hc : (c : 𝒜) = levelafC E D) :
    Finite (𝒮 ⧸ Ideal.span {c}) := by
  classical
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  obtain ⟨T, hT, hTsub, hTres⟩ := levelaf_adele_res D hD
  have : Finite T := hT.to_subtype
  let ψ : (Fin m → T) → 𝒮 ⧸ Ideal.span {c} := fun t => Ideal.Quotient.mk _
    ⟨∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] ((t j : T) : FiniteAdeleRing (𝓞 F) F),
      sum_mem fun j _ => levelaf_tmul_mem _ (hTsub (t j).2)⟩
  refine Finite.of_surjective ψ ?_
  intro q
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr, hs⟩ := levelaf_decomp b hb s.2
  choose t ht y hy hty using fun j => hTres (r j) (hr j)
  refine ⟨fun j => ⟨t j, ht j⟩, ?_⟩
  simp only [ψ]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  refine ⟨⟨-∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] y j,
    neg_mem (sum_mem fun j _ => levelaf_tmul_mem _ (hy j))⟩, ?_⟩
  apply Subtype.ext
  simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, hc]
  rw [hs]
  simp only [hty, TensorProduct.tmul_add, Finset.sum_add_distrib, levelafC, Finset.sum_mul,
    neg_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  simp only [mul_comm (y _)]
  abel
end Formalism.UG.P
