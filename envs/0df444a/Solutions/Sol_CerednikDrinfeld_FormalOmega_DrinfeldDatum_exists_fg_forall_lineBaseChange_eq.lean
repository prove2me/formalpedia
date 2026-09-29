-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_fg_forall_lineBaseChange_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6ed77582-2e52-5c1e-9874-02bff53b17b6

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_deligneDatum_away_forall_map
import Theorems.Thm_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcQuadrupleCor

section Away

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

abbrev toAway (r : B) : B →ₐ[𝒪] Localization.Away r :=
  IsScalarTower.toAlgHom 𝒪 B (Localization.Away r)

abbrev awayMap (r : B) (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K (Localization.Away r) M :=
  AlgebraTensorModule.rTensor 𝒪 (↥M.1) (Algebra.linearMap B (Localization.Away r))

scoped instance awayMap_isLocalizedModule (r : B) (M : FullLattice 𝒪 K) :
    IsLocalizedModule (Submonoid.powers r) (awayMap (𝒪 := 𝒪) (K := K) r M) := by
  infer_instance

theorem awayMap_apply (r : B) (M : FullLattice 𝒪 K) (y : latticeBaseChange 𝒪 K B M) :
    awayMap r M y = LinearMap.rTensor (↥M.1) (toAway (𝒪 := 𝒪) r).toLinearMap y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b v => rfl

theorem exists_fg_localized'_eq {R : Type} [CommRing R] (S : Submonoid R) (R' : Type) [CommRing R'] [Algebra R R']
    [IsLocalization S R'] {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W] [Module R' W]
    [IsScalarTower R R' W] (f : V →ₗ[R] W) [IsLocalizedModule S f] (P : Submodule R' W) (hP : P.FG) :
    ∃ N : Submodule R V, N.FG ∧ N.localized' R' S f = P := by
  classical
  obtain ⟨G, hG⟩ := hP

  have hnum : ∀ w : W, ∃ v : V, ∃ s : S, IsLocalizedModule.mk' f v s = w := by
    intro w
    obtain ⟨⟨v, s⟩, h⟩ := IsLocalizedModule.mk'_surjective S f w
    exact ⟨v, s, h⟩
  choose num den hnd using hnum
  refine ⟨Submodule.span R (num '' (G : Set W)), ⟨G.image num, by rw [Finset.coe_image]⟩, ?_⟩
  rw [Submodule.localized'_span, ← hG]
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩

    have h1 : f (num w) = (den w : R) • w := by
      have := IsLocalizedModule.mk'_cancel' (S := S) f (num w) (den w)
      rw [hnd w] at this
      rw [← this, Submonoid.smul_def]
    rw [h1, ← algebraMap_smul R' (den w : R) w]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hw)
  · refine Submodule.span_le.mpr fun w hw => ?_

    obtain ⟨u, hu⟩ := IsLocalization.map_units R' (den w)
    have h1 : f (num w) = (den w : R) • w := by
      have := IsLocalizedModule.mk'_cancel' (S := S) f (num w) (den w)
      rw [hnd w] at this
      rw [← this, Submonoid.smul_def]
    have h2 : w = ((u⁻¹ : R'ˣ) : R') • f (num w) := by
      rw [h1, ← algebraMap_smul R' (den w : R) w, ← hu, smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨num w, ⟨w, hw, rfl⟩, rfl⟩)

end Away

section FG

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {π : 𝒪}
variable {C : Type} [CommRing C] [Algebra 𝒪 C]

scoped instance finite_lattice (M : FullLattice 𝒪 K) : Module.Finite 𝒪 ↥M.1 :=
  Module.Finite.iff_fg.mpr M.2.1

scoped instance finite_latticeBaseChange (M : FullLattice 𝒪 K) : Module.Finite C (latticeBaseChange 𝒪 K C M) :=
  inferInstanceAs (Module.Finite C (C ⊗[𝒪] ↥M.1))

theorem fg_line (d : DeligneDatum (K := K) π C) (L : FullLattice 𝒪 K) : (d.line L).FG := by
  haveI := d.invertible L
  haveI : Module.FinitePresentation C (latticeBaseChange 𝒪 K C L ⧸ d.line L) :=
    Module.finitePresentation_of_projective _ _
  have h := Module.FinitePresentation.fg_ker (d.line L).mkQ (Submodule.mkQ_surjective _)
  rwa [Submodule.ker_mkQ] at h

end FG

section Transit

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

def awayToLoc (r : B) (y : PrimeSpectrum B) (hr : r ∉ y.asIdeal) : Localization.Away r →ₐ[𝒪] locRing B y :=
  IsLocalization.liftAlgHom (M := Submonoid.powers r) (f := toLocRing B y) fun s => by
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp s.2
    have hs : (s : B) ∉ y.asIdeal := by
      rw [← hn]
      exact fun h => hr (y.2.mem_of_pow_mem n h)
    exact IsLocalization.map_units (locRing B y) (⟨s, hs⟩ : y.asIdeal.primeCompl)

theorem awayToLoc_algebraMap (r : B) (y : PrimeSpectrum B) (hr : r ∉ y.asIdeal) (b : B) :
    awayToLoc (𝒪 := 𝒪) r y hr (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b := by
  rw [awayToLoc, IsLocalization.liftAlgHom_apply]
  exact IsLocalization.lift_eq _ b

theorem comp_toAway_eq (r : B) (y : PrimeSpectrum B) (g : Localization.Away r →ₐ[𝒪] locRing B y)
    (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b) :
    g.comp (toAway (𝒪 := 𝒪) r) = toLocRing B y := by
  ext b
  exact hg b

theorem span_image_rTensor_span {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (M : FullLattice 𝒪 K)
    (S : Set (latticeBaseChange 𝒪 K B M)) :
    Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' (Submodule.span B S : Set (latticeBaseChange 𝒪 K B M))) =
      Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' S) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨z, hz, rfl⟩
    induction hz using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
    | smul b w _ hw =>
      rw [rTensor_smul_left f M b w]
      exact Submodule.smul_mem _ _ hw
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem lineBaseChange_toLocRing_eq (r : B) (y : PrimeSpectrum B) (g : Localization.Away r →ₐ[𝒪] locRing B y)
    (hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b)
    (L : FullLattice 𝒪 K) (N : Submodule B (latticeBaseChange 𝒪 K B L)) :
    lineBaseChange (toLocRing B y) L N =
      lineBaseChange g L (N.localized' (Localization.Away r) (Submonoid.powers r) (awayMap r L)) := by
  have hfun : (⇑(awayMap (𝒪 := 𝒪) (K := K) r L) : latticeBaseChange 𝒪 K B L → latticeBaseChange 𝒪 K (Localization.Away r) L) =
      ⇑(LinearMap.rTensor (↥L.1) (toAway (𝒪 := 𝒪) r).toLinearMap) :=
    funext fun z => awayMap_apply r L z
  rw [Submodule.localized'_eq_span, hfun, lineBaseChange, lineBaseChange, span_image_rTensor_span, ← Set.image_comp]
  congr 1
  refine Set.image_congr fun z _ => ?_
  change LinearMap.rTensor (↥L.1) (toLocRing B y).toLinearMap z =
    LinearMap.rTensor (↥L.1) g.toLinearMap (LinearMap.rTensor (↥L.1) (toAway (𝒪 := 𝒪) r).toLinearMap z)
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
  congr 2
  rw [← comp_toAway_eq r y g hg]
  rfl

end Transit

section Main

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem main (hπ : Irreducible π) (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ N : Submodule B (latticeBaseChange 𝒪 K B L), N.FG ∧
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal → ∀ dy : DeligneDatum (K := K) π (locRing B y),
        LinearMap.ker (Q.u₀ y) = dy.line (Q.L₀ y) → LinearMap.ker (Q.u₁ y) = dy.line (Q.L₁ y) →
        dy.InEdgeChart π (Q.L₀ y) (Q.L₁ y) →
          lineBaseChange (toLocRing B y) L N = dy.line L := by

  obtain ⟨r, hr, d, hd⟩ :=
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map hπ hB Q x

  obtain ⟨N, hNfg, hN⟩ := exists_fg_localized'_eq (Submonoid.powers r) (Localization.Away r) (awayMap r L)
    (d.line L) (fg_line d L)
  refine ⟨r, hr, N, hNfg, fun y hy dy h₀ h₁ hchart => ?_⟩

  let g : Localization.Away r →ₐ[𝒪] locRing B y := awayToLoc r y hy
  have hg : ∀ b : B, g (algebraMap B (Localization.Away r) b) = algebraMap B (locRing B y) b :=
    awayToLoc_algebraMap r y hy
  obtain ⟨hk₀, hk₁, hch⟩ := hd y hy g hg
  have hdy : dy = d.map π g :=
    CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq hπ (d.map π g) dy (Q.L₀ y) (Q.L₁ y) hch
      (by rw [← hk₁, h₁]) (by rw [← hk₀, h₀])
  rw [hdy, lineBaseChange_toLocRing_eq r y g hg L N, hN]
  rfl

end Main

end P2mKcQuadrupleCor
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq.P2mKcQuadrupleCor"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq.P2mKcQuadrupleCor"

open P2mKcQuadrupleCor in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (L : FullLattice 𝒪 K) :
    ∃ r : B, r ∉ x.asIdeal ∧ ∃ N : Submodule B (latticeBaseChange 𝒪 K B L), N.FG ∧
      ∀ (y : PrimeSpectrum B), r ∉ y.asIdeal → ∀ dy : DeligneDatum (K := K) π (locRing B y),
        LinearMap.ker (Q.u₀ y) = dy.line (Q.L₀ y) → LinearMap.ker (Q.u₁ y) = dy.line (Q.L₁ y) →
        dy.InEdgeChart π (Q.L₀ y) (Q.L₁ y) →
          lineBaseChange (toLocRing B y) L N = dy.line L :=
  main hπ hB Q x L

end S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_fg_forall_lineBaseChange_eq (solution)
