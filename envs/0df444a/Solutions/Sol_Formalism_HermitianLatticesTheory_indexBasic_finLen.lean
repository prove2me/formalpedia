-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.indexBasic_finLen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:32:59.499303+00:00
-- url     : https://prove2.me/submissions/9c152a95-0f72-4128-b93d-4e59a7ee19e1

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_key
import Theorems.Thm_Formalism_HermitianLatticesTheory_indexBasic_smul_locP
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R) [p.IsPrime]
    (X Y : Submodule R W) (hX : X.FG) {d : R} (hd : d ∈ nonZeroDivisors R)
    (hdY : ∀ x ∈ X, d • x ∈ Y) :
    IsFiniteLength R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) := by
  set P := localization₂ p X with hP
  set Q := (localization₂ p Y).comap P.subtype with hQ
  have hXP : X ≤ P := locBasic_le_locS _ X
  have hdP : ∀ x ∈ P, d • x ∈ localization₂ p Y := by
    rintro x ⟨s, hs, hsx⟩
    exact ⟨s, hs, by rw [smul_comm]; exact hdY _ hsx⟩
  have hkill : ∀ m : ↥P ⧸ Q, d • m = 0 := by
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hdP x.1 x.2
  let ψ : ↥X →ₗ[R] ↥P ⧸ Q := Q.mkQ ∘ₗ Submodule.inclusion hXP
  have hsurj : Function.Surjective ψ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, hsx⟩ := x.2
      obtain ⟨n, t, u, htu⟩ := indexBasic_key hd s
      refine ⟨⟨t • s • (x : W), X.smul_mem t hsx⟩, ?_⟩
      show Q.mkQ _ = Submodule.Quotient.mk x
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      show (t • s • (x : W) - x) ∈ localization₂ p Y
      have hsn : s ^ n ∉ p := fun h => hs (‹p.IsPrime›.mem_of_pow_mem n h)
      apply indexBasic_smul_locP p Y hsn
      have e : s ^ n • (t • s • (x : W) - x) = - (u • (d • (x : W))) := by
        linear_combination (norm := module) -(htu • (x : W))
      rw [e]
      exact (localization₂ p Y).neg_mem ((localization₂ p Y).smul_mem u (hdP x.1 x.2))
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hX
  have hgX : ∀ i, g i ∈ X := fun i => hg ▸ Submodule.subset_span (Set.mem_range_self i)
  let m : Fin n → ↥P ⧸ Q := fun i => ψ ⟨g i, hgX i⟩
  let F : (Fin n → R ⧸ Ideal.span {d}) →ₗ[R] ↥P ⧸ Q :=
    ∑ i, ((Ideal.span {d}).liftQ (LinearMap.toSpanSingleton R _ (m i)) (by
      intro r hr
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      simp [LinearMap.mem_ker, mul_smul, hkill])) ∘ₗ LinearMap.proj i
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨x, rfl⟩ := hsurj z
    have hx : (x : W) ∈ Submodule.span R (Set.range g) := hg ▸ x.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
    refine ⟨fun i => Submodule.Quotient.mk (c i), ?_⟩
    have hx' : x = ∑ i, c i • (⟨g i, hgX i⟩ : ↥X) := Subtype.ext (by simp [hc])
    rw [hx', map_sum]
    simp only [F, m]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply, map_smul]
  have hfin : IsFiniteLength R (Fin n → R ⧸ Ideal.span {d}) := by
    have hfl : IsFiniteLength R (R ⧸ Ideal.span {d}) := isFiniteLength_quotient_span_singleton R hd
    obtain ⟨h1, h2⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hfin.of_surjective hF
end Formalism.HermitianLatticesTheory
