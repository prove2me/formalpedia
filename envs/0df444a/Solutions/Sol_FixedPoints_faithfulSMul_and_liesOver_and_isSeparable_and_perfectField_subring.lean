-- Prove2me | solution 1 for FixedPoints.faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/77351f8a-8e58-5cb4-a379-12185e91b4d5

import Mathlib
import Definitions.Def_Mathlib_RingTheory_Valuation_UpperRamificationGroup
import Definitions.Def_Mathlib_RingTheory_Invariant_FixedSubringLocal
import Definitions.Def_RamificationChain_Wild
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring

set_option autoImplicit false

namespace FixedPoints
p2m_export "FixedPoints" "subfield isSeparable minpoly subring subgroup toAlgAut_bijective normal maximalIdeal_subring_eq_comap"
namespace Frame
p2m_open "FixedPoints"

section frac

variable {R : Type*} [CommRing R] [IsDomain R] {G : Type*} [Group G] [MulSemiringAction G R]

theorem map_nonZeroDivisors_eq (σ : G) :
    (nonZeroDivisors R).map (MulSemiringAction.toRingEquiv G R σ).toMonoidHom = nonZeroDivisors R := by
  ext x
  simp only [Submonoid.mem_map, mem_nonZeroDivisors_iff_ne_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    change σ • y ≠ 0
    rwa [Ne, smul_eq_zero_iff_eq]
  · intro hx
    refine ⟨σ⁻¹ • x, ?_, ?_⟩
    · rwa [Ne, smul_eq_zero_iff_eq]
    · change σ • (σ⁻¹ • x) = x
      exact smul_inv_smul _ _

noncomputable def fracAut (σ : G) : FractionRing R ≃+* FractionRing R :=
  IsLocalization.ringEquivOfRingEquiv (M := nonZeroDivisors R) (T := nonZeroDivisors R) (FractionRing R) (FractionRing R)
    (MulSemiringAction.toRingEquiv G R σ) (map_nonZeroDivisors_eq σ)

theorem fracAut_algebraMap (σ : G) (x : R) :
    fracAut σ (algebraMap R (FractionRing R) x) = algebraMap R (FractionRing R) (σ • x) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ x

theorem fracAut_one : fracAut (1 : G) = RingEquiv.refl (FractionRing R) := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors R) ?_
  ext x
  simp [fracAut_algebraMap]

theorem fracAut_mul (σ τ : G) : fracAut (R := R) (σ * τ) = (fracAut τ).trans (fracAut σ) := by
  apply RingEquiv.toRingHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors R) ?_
  ext x
  simp [fracAut_algebraMap, mul_smul]

noncomputable def fracAutHom : G →* RingAut (FractionRing R) where
  toFun := fracAut
  map_one' := fracAut_one
  map_mul' σ τ := by rw [fracAut_mul]; rfl

noncomputable scoped instance mulSemiringActionFractionRing : MulSemiringAction G (FractionRing R) :=
  MulSemiringAction.compHom _ (fracAutHom (R := R))

theorem smul_frac_def (σ : G) (y : FractionRing R) : σ • y = fracAut σ y := rfl

@[scoped simp] theorem smul_algebraMap (σ : G) (x : R) : σ • algebraMap R (FractionRing R) x = algebraMap R (FractionRing R) (σ • x) :=
  fracAut_algebraMap σ x

theorem faithfulSMul_fractionRing [FaithfulSMul G R] : FaithfulSMul G (FractionRing R) := by
  refine ⟨fun {σ τ} h => FaithfulSMul.eq_of_smul_eq_smul (α := R) fun x => IsFractionRing.injective R (FractionRing R) ?_⟩
  rw [← smul_algebraMap, ← smul_algebraMap, h]

variable (H : Subgroup G) [Finite H]

theorem exists_prod_smul (s : R) (hs : s ≠ 0) :
    ∃ N : R, (∀ h : H, (h : G) • N = N) ∧ N ≠ 0 ∧ ∃ u : R, N = s * u := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  refine ⟨∏ h : H, (h : G) • s, fun h => ?_, ?_, ?_⟩
  · rw [Finset.smul_prod']
    exact Fintype.prod_equiv (Equiv.mulLeft h) _ _ (fun k => by simp [mul_smul])
  · rw [Finset.prod_ne_zero_iff]
    intro h _
    rwa [Ne, smul_eq_zero_iff_eq]
  · refine ⟨∏ h ∈ Finset.univ.erase (1 : H), (h : G) • s, ?_⟩
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : H))]
    simp

theorem exists_eq_div_of_forall_smul_eq (y : FractionRing R) (hy : ∀ h : H, (h : G) • y = y) :
    ∃ c N : R, (∀ h : H, (h : G) • c = c) ∧ (∀ h : H, (h : G) • N = N) ∧ N ≠ 0 ∧
      y * algebraMap R (FractionRing R) N = algebraMap R (FractionRing R) c := by
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) y
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  obtain ⟨N, hNfix, hN0, u, hNu⟩ := exists_prod_smul H s hs0
  have hsK : algebraMap R (FractionRing R) s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  refine ⟨a * u, N, fun h => ?_, hNfix, hN0, ?_⟩
  · apply IsFractionRing.injective R (FractionRing R)
    rw [← smul_algebraMap]
    have key : algebraMap R (FractionRing R) (a * u) = algebraMap R _ a / algebraMap R _ s * algebraMap R _ N := by
      rw [hNu, map_mul, map_mul]; field_simp
    rw [key, smul_mul', hy h, smul_algebraMap, hNfix h]
  · rw [hNu, map_mul, map_mul]; field_simp

theorem smul_eq_self_of_forall_fixedPoints (σ : G) (hσ : ∀ s : FixedPoints.subring R H, σ • (s : R) = s)
    (y : FractionRing R) (hy : ∀ h : H, (h : G) • y = y) : σ • y = y := by
  obtain ⟨c, N, hc, hN, hN0, hyN⟩ := exists_eq_div_of_forall_smul_eq H y hy
  have hNK : algebraMap R (FractionRing R) N ≠ 0 := fun h => hN0 (IsFractionRing.injective R (FractionRing R) (by rw [h, map_zero]))
  have hy' : y = algebraMap R _ c / algebraMap R _ N := by rw [eq_div_iff hNK, hyN]
  have hc' : σ • c = c := hσ ⟨c, fun h => hc h⟩
  have hN' : σ • N = N := hσ ⟨N, fun h => hN h⟩
  rw [hy', smul_frac_def, map_div₀, ← smul_frac_def, ← smul_frac_def, smul_algebraMap, smul_algebraMap, hc', hN']

end frac

end FixedPoints.Frame
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints"

namespace FixedPoints
p2m_export "FixedPoints" "subfield isSeparable minpoly subring subgroup toAlgAut_bijective normal maximalIdeal_subring_eq_comap"
namespace Frame
p2m_open "FixedPoints"

section galois

variable {R : Type*} [CommRing R] [IsDomain R] {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]

theorem mem_of_forall_fixedPoints (H : Subgroup G) (σ : G) (hσ : ∀ s : FixedPoints.subring R H, σ • (s : R) = s) : σ ∈ H := by
  haveI : FaithfulSMul G (FractionRing R) := faithfulSMul_fractionRing
  let K := FractionRing R
  let F₀ := FixedPoints.subfield G K
  let φ : G →* (K ≃ₐ[F₀] K) := MulSemiringAction.toAlgAut G F₀ K
  have hφ : Function.Bijective φ := FixedPoints.toAlgAut_bijective G K
  have hφapp : ∀ (g : G) (y : K), φ g y = g • y := fun g y => rfl
  let H' : Subgroup (K ≃ₐ[F₀] K) := H.map φ

  have hfix : φ σ ∈ (IntermediateField.fixedField H').fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    rw [hφapp]
    refine smul_eq_self_of_forall_fixedPoints H σ hσ y (fun h => ?_)
    have := hy ⟨φ h, Subgroup.mem_map_of_mem φ h.2⟩
    exact this
  rw [IntermediateField.fixingSubgroup_fixedField] at hfix
  obtain ⟨h, hh, hhσ⟩ := Subgroup.mem_map.mp hfix
  rw [← hφ.1 hhσ]
  exact hh

theorem faithfulSMul_quotient (H : Subgroup G) [H.Normal] : FaithfulSMul (G ⧸ H) (FixedPoints.subring R H) := by
  refine ⟨fun {x y} hxy => ?_⟩
  induction x using QuotientGroup.induction_on with
  | H σ =>
    induction y using QuotientGroup.induction_on with
    | H τ =>
      rw [QuotientGroup.eq]
      refine mem_of_forall_fixedPoints (R := R) H (σ⁻¹ * τ) (fun s => ?_)
      have := congrArg (fun z : FixedPoints.subring R H => (z : R)) (hxy s)
      change σ • (s : R) = τ • (s : R) at this
      rw [mul_smul, ← this, inv_smul_smul]

end galois
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"

end FixedPoints.Frame
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"

namespace FixedPoints
p2m_export "FixedPoints" "subfield isSeparable minpoly subring subgroup toAlgAut_bijective normal maximalIdeal_subring_eq_comap"
namespace Frame
p2m_open "FixedPoints"

open IsLocalRing Polynomial

section residue

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R] (H : Subgroup G) [H.Normal]

def toTop (t : FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)) : FixedPoints.subring R G :=
  ⟨((t : FixedPoints.subring R H) : R), fun g => by
    have := t.2 (QuotientGroup.mk g)
    have := congrArg (fun z : FixedPoints.subring R H => (z : R)) this
    exact this⟩

def ofTop (a : FixedPoints.subring R G) : FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) :=
  ⟨⟨(a : R), fun h => a.2 (h : G)⟩, fun q => QuotientGroup.induction_on q fun g => Subtype.ext (a.2 g)⟩

theorem toTop_ofTop (a : FixedPoints.subring R G) : toTop H (ofTop H a) = a := Subtype.ext rfl

def toTopHom : FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) →+* FixedPoints.subring R G where
  toFun := toTop H
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem toTopHom_surjective : Function.Surjective (toTopHom H (R := R)) := fun a => ⟨ofTop H a, toTop_ofTop H a⟩

def inclHom : FixedPoints.subring R G →+* FixedPoints.subring R H where
  toFun a := ⟨(a : R), fun h => a.2 (h : G)⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem liesOver_quotient :
    (maximalIdeal (FixedPoints.subring R H)).LiesOver (maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H))) :=
  ⟨by rw [Ideal.under_def, FixedPoints.maximalIdeal_subring_eq_comap]; rfl⟩

theorem liesOver_top : (maximalIdeal R).LiesOver (maximalIdeal (FixedPoints.subring R H)) :=
  ⟨by rw [Ideal.under_def, FixedPoints.maximalIdeal_subring_eq_comap]; rfl⟩

theorem mem_maximalIdeal_sub_iff (s : FixedPoints.subring R H) : s ∈ maximalIdeal (FixedPoints.subring R H) ↔ (s : R) ∈ maximalIdeal R := by
  rw [FixedPoints.maximalIdeal_subring_eq_comap, Ideal.mem_comap]; rfl

theorem mem_maximalIdeal_subsub_iff (t : FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)) :
    t ∈ maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)) ↔ ((t : FixedPoints.subring R H) : R) ∈ maximalIdeal R := by
  rw [FixedPoints.maximalIdeal_subring_eq_comap, Ideal.mem_comap, ← mem_maximalIdeal_sub_iff H]; rfl

omit [H.Normal] in
theorem mem_maximalIdeal_top_iff (a : FixedPoints.subring R G) : a ∈ maximalIdeal (FixedPoints.subring R G) ↔ (a : R) ∈ maximalIdeal R := by
  rw [FixedPoints.maximalIdeal_subring_eq_comap, Ideal.mem_comap]; rfl

def psi : FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) ⧸ maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)) →+*
    FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G) :=
  Ideal.quotientMap _ (toTopHom H) (fun t ht => by
    rw [Ideal.mem_comap, mem_maximalIdeal_top_iff]
    exact (mem_maximalIdeal_subsub_iff H t).1 ht)

theorem psi_surjective : Function.Surjective (psi H (R := R)) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨t, rfl⟩ := toTopHom_surjective H a
  exact ⟨Ideal.Quotient.mk _ t, rfl⟩

def phi : FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G) →+* FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H) :=
  Ideal.quotientMap _ (inclHom H) (fun a ha => by
    rw [Ideal.mem_comap, mem_maximalIdeal_sub_iff]
    exact (mem_maximalIdeal_top_iff a).1 ha)

end residue
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"

section separable

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R] (H : Subgroup G) [H.Normal]
  [(maximalIdeal R).LiesOver (maximalIdeal (FixedPoints.subring R G))]
  [Algebra.IsSeparable (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) (R ⧸ maximalIdeal R)]

theorem isSeparable_quotient
    [(maximalIdeal (FixedPoints.subring R H)).LiesOver (maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))] :
    Algebra.IsSeparable
      (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) ⧸ maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))
      (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H)) := by
  letI : Field (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) ⧸ maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H))) :=
    Ideal.Quotient.field _
  letI : Field (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H)) := Ideal.Quotient.field _
  letI : Field (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) := Ideal.Quotient.field _
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  haveI := liesOver_top H (R := R)
  rw [Algebra.isSeparable_def]
  intro x
  let ι := algebraMap (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H)) (R ⧸ maximalIdeal R)
  have hι : Function.Injective ι := ι.injective
  have hsep : (_root_.minpoly (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) (ι x)).Separable :=
    Algebra.IsSeparable.isSeparable _ _
  obtain ⟨Q, hQ⟩ := Polynomial.map_surjective (psi H (R := R)) (psi_surjective H) (_root_.minpoly _ (ι x))
  have hQsep : Q.Separable := (Polynomial.separable_map (psi H (R := R))).1 (hQ ▸ hsep)
  refine hQsep.of_dvd (_root_.minpoly.dvd _ x ?_)
  apply hι
  have hcomp : ι.comp (algebraMap _ (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H))) =
      (algebraMap (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) (R ⧸ maximalIdeal R)).comp (psi H) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun t => ?_)
    rfl
  rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, ← Polynomial.eval₂_map, hQ]
  exact _root_.minpoly.aeval _ _

theorem isSeparable_top :
    @Algebra.IsSeparable (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H)) (R ⧸ maximalIdeal R) _ _
      (@Ideal.Quotient.algebraOfLiesOver _ _ _ _ _ (maximalIdeal R) (maximalIdeal (FixedPoints.subring R H)) (liesOver_top H)) := by
  letI : Field (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H)) := Ideal.Quotient.field _
  letI : Field (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) := Ideal.Quotient.field _
  letI : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  haveI := liesOver_top H (R := R)
  rw [Algebra.isSeparable_def]
  intro y
  have hsep : (_root_.minpoly (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) y).Separable :=
    Algebra.IsSeparable.isSeparable _ _
  have hmap := (Polynomial.separable_map (phi H)).2 hsep
  refine hmap.of_dvd (_root_.minpoly.dvd _ y ?_)
  have hcomp : (algebraMap (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H)) (R ⧸ maximalIdeal R)).comp (phi H) =
      algebraMap (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) (R ⧸ maximalIdeal R) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  exact _root_.minpoly.aeval _ _

end separable
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"

section perfect

variable {R : Type*} [CommRing R] [IsLocalRing R] {G : Type*} [Group G] [MulSemiringAction G R] (H : Subgroup G) [H.Normal]
  [(maximalIdeal R).LiesOver (maximalIdeal (FixedPoints.subring R G))]
  [Algebra.IsSeparable (FixedPoints.subring R G ⧸ maximalIdeal (FixedPoints.subring R G)) (R ⧸ maximalIdeal R)]
  [PerfectField (ResidueField R)]

theorem perfectField_residueField : PerfectField (ResidueField (FixedPoints.subring R H)) := by
  haveI := liesOver_top H (R := R)
  letI : Algebra (ResidueField (FixedPoints.subring R H)) (ResidueField R) :=
    inferInstanceAs (@Algebra (FixedPoints.subring R H ⧸ maximalIdeal (FixedPoints.subring R H)) (R ⧸ maximalIdeal R) _ _)
  haveI : Algebra.IsSeparable (ResidueField (FixedPoints.subring R H)) (ResidueField R) := isSeparable_top H
  exact perfectField_of_isSeparable_of_perfectField_top (ResidueField (FixedPoints.subring R H)) (ResidueField R)

end perfect
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"

end FixedPoints.Frame
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"
p2m_reactivate "P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring.FixedPoints.Frame"

open FixedPoints.Frame IsLocalRing in

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {G : Type*} [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
    [(IsLocalRing.maximalIdeal R).LiesOver (IsLocalRing.maximalIdeal (FixedPoints.subring R G))]
    [Algebra.IsSeparable
      (FixedPoints.subring R G ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R G))
      (R ⧸ IsLocalRing.maximalIdeal R)]
    [PerfectField (IsLocalRing.ResidueField R)]
    (H : Subgroup G) [H.Normal] :
    FaithfulSMul (G ⧸ H) (FixedPoints.subring R H) ∧
    PerfectField (IsLocalRing.ResidueField (FixedPoints.subring R H)) ∧
    ∃ (_ : (IsLocalRing.maximalIdeal (FixedPoints.subring R H)).LiesOver
      (IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))),
      Algebra.IsSeparable
        (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H) ⧸
          IsLocalRing.maximalIdeal (FixedPoints.subring (FixedPoints.subring R H) (G ⧸ H)))
        (FixedPoints.subring R H ⧸ IsLocalRing.maximalIdeal (FixedPoints.subring R H)) := by
  refine ⟨faithfulSMul_quotient H, perfectField_residueField H, liesOver_quotient H, ?_⟩
  haveI := liesOver_quotient H (R := R)
  exact isSeparable_quotient H

end S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring
end P2MW
export P2MW.S_FixedPoints_faithfulSMul_and_liesOver_and_isSeparable_and_perfectField_subring (solution)
