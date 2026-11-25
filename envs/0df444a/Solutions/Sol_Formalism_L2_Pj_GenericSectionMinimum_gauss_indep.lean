-- Prove2me | solution 1 for Formalism.L2.Pj.GenericSectionMinimum.gauss_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:41:29.778715+00:00
-- url     : https://prove2.me/submissions/95dca1f7-56dc-498d-a830-05bb9b7fe3b7

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PowMapMemOfPowMulMem
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DerAeval
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_TotalDegreePderivLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenericSectionMinimum
open IsLocalRing Cardinal
namespace Formalism.L2.Pj.GenericSectionMinimum
theorem _root_.solution {K Ω U τ : Type} [Field K] [Field Ω] [Field U] [Algebra K Ω] [Algebra Ω U] [Algebra K U]
    [IsScalarTower K Ω U] (V : ValuationSubring U) (T : τ → U) (hT : ∀ q, T q ∈ V)
    (hG : ∀ Q : MvPolynomial τ K, (∀ α, V.valuation (algebraMap K U (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap K U (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1) :
    letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω U)
    letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
    letI : Algebra (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V) :=
      ((algebraMap _ (ResidueField V)).comp (algebraMap _ (ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
    AlgebraicIndependent (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
      (fun j => residue V ⟨T j, hT j⟩) := by
  letI _iW := ReciprocityTheory.MultiplicativeHeights.residueAlgebra V (algebraMap Ω U)
  letI _io := ReciprocityTheory.MultiplicativeHeights.residueAlgebra (V.comap (algebraMap Ω U)) (algebraMap K Ω)
  letI _ia : Algebra (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V) :=
    ((algebraMap _ (ResidueField V)).comp
      (algebraMap _ (ResidueField (V.comap (algebraMap Ω U))))).toAlgebra
  classical
  have f0def : ∀ x : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω),
      (((ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
        (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) x : V) : U) =
        algebraMap K U (x : K) := by
    intro x
    show algebraMap Ω U (algebraMap K Ω (x : K)) = _
    exact (IsScalarTower.algebraMap_apply K Ω U _).symm
  have hcomp : ∀ x : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω),
      algebraMap (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω))) (ResidueField V)
        (residue _ x) =
      residue V ((ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
        (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) x) := by
    intro x
    simp only [_ia, _iW, _io, ReciprocityTheory.MultiplicativeHeights.residueAlgebra, RingHom.algebraMap_toAlgebra,
      RingHom.comp_apply, IsLocalRing.ResidueField.map_residue] <;> rfl
  set f0 := (ReciprocityTheory.MultiplicativeHeights.comapInclusion V (algebraMap Ω U)).comp
    (ReciprocityTheory.MultiplicativeHeights.comapInclusion (V.comap (algebraMap Ω U)) (algebraMap K Ω)) with hf0
  refine (injective_iff_map_eq_zero (MvPolynomial.aeval
    (R := ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
    (fun j => residue V ⟨T j, hT j⟩))).mpr ?_
  intro R hR
  by_contra hR0
  obtain ⟨Q', rfl⟩ := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective R
  have hqU : ((MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q' : V) : U) =
      MvPolynomial.aeval T
        (MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q') := by
    have e1 := MvPolynomial.eval₂_comp_left V.subtype f0 (fun j => (⟨T j, hT j⟩ : V)) Q'
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e2 : V.subtype.comp f0 =
        (algebraMap K U).comp ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype :=
      RingHom.ext fun x => f0def x
    rw [← e2]
    exact e1
  have hres : residue V (MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q') =
      MvPolynomial.aeval (fun j => residue V ⟨T j, hT j⟩) (MvPolynomial.map (residue _) Q') := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e1 := MvPolynomial.eval₂_comp_left (residue V) f0 (fun j => (⟨T j, hT j⟩ : V)) Q'
    have e2 : (residue V).comp f0 =
        (algebraMap (ResidueField ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)))
          (ResidueField V)).comp (residue _) :=
      RingHom.ext fun x => (hcomp x).symm
    rw [← e2]
    exact e1
  have hlt : V.valuation ((MvPolynomial.eval₂ f0 (fun j => (⟨T j, hT j⟩ : V)) Q' : V) : U) < 1 := by
    rw [← ValuationSubring.valuation_lt_one_iff, ← IsLocalRing.residue_eq_zero_iff, hres]
    exact hR
  have hc : ∀ α, (MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α =
      ((Q'.coeff α : (V.comap (algebraMap Ω U)).comap (algebraMap K Ω)) : K) := fun α =>
    MvPolynomial.coeff_map _ _ _
  have hle : ∀ α, V.valuation (algebraMap K U
      ((MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α)) ≤ 1 := by
    intro α
    rw [hc, ← f0def]
    exact V.valuation_le_one _
  have hex : ∃ α, V.valuation (algebraMap K U
      ((MvPolynomial.map ((V.comap (algebraMap Ω U)).comap (algebraMap K Ω)).subtype Q').coeff α)) = 1 := by
    obtain ⟨α, hα⟩ := MvPolynomial.ne_zero_iff.mp hR0
    refine ⟨α, ?_⟩
    rw [MvPolynomial.coeff_map] at hα
    have hu : IsUnit (Q'.coeff α) := by
      by_contra hnu
      apply hα
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
    rw [hc, ← f0def]
    exact (V.valuation_eq_one_iff _).mp (hu.map f0)
  have h1 := hG _ hle hex
  rw [← hqU] at h1
  rw [h1] at hlt
  exact lt_irrefl _ hlt
end Formalism.L2.Pj.GenericSectionMinimum
