-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.localizedQuotients.akCount_locF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:08.797409+00:00
-- url     : https://prove2.me/submissions/9802d6a0-ecfa-48dc-89f9-9e04d747c12b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsBasisLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulOfMemSmulLocF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_quotLocF_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_form_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_congrP_of_mul_left
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_localizedQuotients_exists_common

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.localizedQuotients
open LocalSpans idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.localizedQuotients
theorem _root_.solution (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : akCount h (locF 𝔭 L) 𝔭 k = akCount h L 𝔭 k := by
  have := h𝔭.isPrime
  unfold akCount
  symm
  refine Nat.card_congr ((quotLocF h𝔭 L k).conj.toEquiv.subtypeEquiv fun X => ?_)
  have hconj : ∀ q, (quotLocF h𝔭 L k).conj X (quotLocF h𝔭 L k q) = quotLocF h𝔭 L k (X q) := by
    intro q
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
  constructor
  · intro hX x y x' y' hx hy
    obtain ⟨t, ht, htL⟩ := exists_common h𝔭 L ![(x : V), y, x', y'] (by
      intro i; fin_cases i
      · exact x.2
      · exact y.2
      · exact x'.2
      · exact y'.2)
    have key : ∀ (u u' : ↥(locF 𝔭 L)) (hu : ι t • (u : V) ∈ L) (hu' : ι t • (u' : V) ∈ L),
        Submodule.Quotient.mk u' = (quotLocF h𝔭 L k).conj X (Submodule.Quotient.mk u) →
        (Submodule.Quotient.mk (⟨_, hu'⟩ : ↥L) : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
          X (Submodule.Quotient.mk ⟨_, hu⟩) := by
      intro u u' hu hu' e
      apply (quotLocF h𝔭 L k).injective
      rw [← hconj, quotLocF_mk h𝔭 L k _ (le_locF 𝔭 L hu'), quotLocF_mk h𝔭 L k _ (le_locF 𝔭 L hu)]
      have e1 : ∀ (v : ↥(locF 𝔭 L)) (hv : ι t • (v : V) ∈ locF 𝔭 L),
          (Submodule.Quotient.mk (⟨_, hv⟩ : ↥(locF 𝔭 L)) :
            ↥(locF 𝔭 L) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 L))) =
            ι t • Submodule.Quotient.mk v := fun v hv => rfl
      rw [e1, e1, e, map_smul]
    have h1 := hX ⟨_, htL 0⟩ ⟨_, htL 1⟩ ⟨_, htL 2⟩ ⟨_, htL 3⟩ (key x x' (htL 0) (htL 2) hx)
      (key y y' (htL 1) (htL 3) hy)
    have h2 : CongrP 𝔭 k (h (ι t • (x' : V)) (ι t • (y' : V))) (h (ι t • (x : V)) (ι t • (y : V))) := h1
    rw [form_smul hF, form_smul hF] at h2
    exact congrP_of_mul_left h𝔭 (fun hm => (h𝔭.isPrime.mem_or_mem hm).elim ht ht) h2
  · intro hX x y x' y' hx hy
    refine hX ⟨x, le_locF 𝔭 L x.2⟩ ⟨y, le_locF 𝔭 L y.2⟩ ⟨x', le_locF 𝔭 L x'.2⟩ ⟨y', le_locF 𝔭 L y'.2⟩
      ?_ ?_
    · rw [← quotLocF_mk h𝔭 L k x', ← quotLocF_mk h𝔭 L k x, hx]
      exact (hconj _).symm
    · rw [← quotLocF_mk h𝔭 L k y', ← quotLocF_mk h𝔭 L k y, hy]
      exact (hconj _).symm
end Formalism.HermitianLattices.Ext.L3.localizedQuotients
