-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.OrthogonalBases.sup_eq_top_of_mem_hcompl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:23:56.775849+00:00
-- url     : https://prove2.me/submissions/0b4e501b-95f7-421b-a49f-cf05e7a30661

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SupEqTopOfMemHcompl
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SplitPrimeIdeals_comap_eq_comap_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_mem_hcompl_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_comap_eq_comap_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.OrthogonalBases
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.OrthogonalBases
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {u : 𝓞 K} (hu : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    Ideal.span {u} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤ := by
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hu' := (Formalism.HermitianLattices.Ext.L3.WA.mem_hcompl_iff hP.isPrime u).1 hu
  have huQ : u ∈ Q := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Q := le_trans le_sup_right hle
  have hpQ : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    Ideal.map_le_iff_le_comap.1 hext
  have hmax : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  haveI := hQ.isPrime
  have heq : P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    hmax.eq_of_le (inferInstance : (Q.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime).ne_top hpQ
  rcases (comap_eq_comap_iff hK hF hP hQ).1 heq with h | h
  · exact hu'.1 (h ▸ huQ)
  · exact hu'.2 (h ▸ huQ)
end Formalism.HermitianLattices.Ext.L3.OrthogonalBases
