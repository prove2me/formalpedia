-- Prove2me | solution 1 for Formalism.L2.Pj.CompSplitPfD.cspD_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:33.04182+00:00
-- url     : https://prove2.me/submissions/cbd719a8-d7e6-41db-9108-131703345f87

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompFin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfC
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompSplitPfD
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfD_cspD_smooth
import Theorems.Thm_Formalism_L2_Pj_CompSplitPfC_cspC_minimal_unique


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.CompSplitPfD
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Topology
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace Formalism.L2.Pj.CompSplitPfD
theorem _root_.solution (Xo : Moduli Dw l) (c : Coeff l) (x : Xo.XF c) :
    ∃ (Y : Type) (_ : TopologicalSpace Y) (g : Y → Xo.XF c), IsOpenEmbedding g ∧ x ∈ Set.range g ∧
      ∀ a b y : Y, (∀ a', a' ⤳ a → a' = a) → (∀ b', b' ⤳ b → b' = b) → a ⤳ y → b ⤳ y → a = b := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    (Xo.XF c).isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have hsm := cspD_smooth Xo c
  have h1 := HasRingHomProperty.appLE (P := @Smooth)
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp; trivial)
  let ψ : c.F →+* Γ(Xo.XF c, V) :=
    ((pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)).appLE ⊤ V (fun p _ => by simp; trivial)).hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of c.F)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra c.F Γ(Xo.XF c, V) := ψ.toAlgebra
  have : Algebra.Smooth c.F Γ(Xo.XF c, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := c.F)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(Xo.XF c, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) c.F) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) c.F) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))
end Formalism.L2.Pj.CompSplitPfD
