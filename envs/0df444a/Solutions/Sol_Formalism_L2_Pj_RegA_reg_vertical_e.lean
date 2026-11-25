-- Prove2me | solution 1 for Formalism.L2.Pj.RegA.reg_vertical_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:12:48.678601+00:00
-- url     : https://prove2.me/submissions/ee91a2bc-fa03-430a-8f97-005cfa21cb38

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegVert
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_av_point
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_regVert_eq_of_le_height_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_regVert_valuationRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.RegA
open IsLocalRing ReciprocityTheory.ChartRestriction.G.T0
namespace Formalism.L2.Pj.RegA
theorem _root_.solution {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A) (e : A) (he : e ≠ 0)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (hv : Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
  classical
  haveI hAN : IsNoetherianRing A := by
    first
    | infer_instance
    | exact Algebra.FiniteType.isNoetherianRing O A
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖm : ϖ ∈ maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hϖ.not_isUnit
  have hϖA0 : algebraMap O A ϖ ≠ 0 := by
    intro h0
    have h1 : (1 : A) ∈ Submodule.torsion O A := by
      rw [Submodule.mem_torsion_iff]
      refine ⟨⟨ϖ, mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero⟩, ?_⟩
      show ϖ • (1 : A) = 0
      rw [Algebra.smul_def, mul_one, h0]
    rw [Module.Flat.torsion_eq_bot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) f
  have hab' : f * algebraMap A (FractionRing A) (b : A) = algebraMap A (FractionRing A) a := hab
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hbK : algebraMap A (FractionRing A) (b : A) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  have hPc : P.primeCompl ≤ nonZeroDivisors A := by
    first
    | exact Ideal.primeCompl_le_nonZeroDivisors P
    | exact le_nonZeroDivisors_of_noZeroDivisors (fun h => (show (0 : A) ∉ P from h) P.zero_mem)
  have hK : ∀ x y : A, algebraMap A (Localization.AtPrime P) x =
      algebraMap A (Localization.AtPrime P) y → x = y :=
    fun x y h => IsLocalization.injective (Localization.AtPrime P) hPc h
  have hfin : ∀ x s : A, s ∉ P → (b : A) * x = a * s →
      ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
    intro x s hs h
    refine ⟨x, s, hs, ?_⟩
    have h' := congrArg (algebraMap A (FractionRing A)) h
    rw [map_mul, map_mul] at h'
    apply mul_left_cancel₀ hbK
    linear_combination (algebraMap A (FractionRing A) s) * hab' - h'
  haveI hVal : ValuationRing (Localization.AtPrime P) := regVert_valuationRing P hP
  have hmaxL : maximalIdeal (Localization.AtPrime P) =
      P.map (algebraMap A (Localization.AtPrime P)) := by
    first
    | exact Localization.AtPrime.map_eq_maximalIdeal.symm
    | exact (Localization.AtPrime.map_eq_maximalIdeal (I := P)).symm
    | exact (IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)).symm
  have hcase1 : ∀ c : Localization.AtPrime P,
      algebraMap A (Localization.AtPrime P) b * c = algebraMap A (Localization.AtPrime P) a →
      ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by
    intro c hc
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    have hspec := IsLocalization.mk'_spec (Localization.AtPrime P) x s
    apply hfin x s s.2
    apply hK
    rw [map_mul, map_mul]
    linear_combination (algebraMap A (Localization.AtPrime P) s) * hc -
      (algebraMap A (Localization.AtPrime P) b) * hspec
  have hcond : ∃ c : Localization.AtPrime P,
      algebraMap A (Localization.AtPrime P) b * c = algebraMap A (Localization.AtPrime P) a ∨
      algebraMap A (Localization.AtPrime P) a * c = algebraMap A (Localization.AtPrime P) b := by
    first
    | exact ValuationRing.cond _ _
    | exact PreValuationRing.cond _ _
    | exact ValuationRing.cond' _ _
  obtain ⟨c, hc | hc⟩ := hcond
  · exact hcase1 c hc
  by_cases hcu : IsUnit c
  · obtain ⟨u, rfl⟩ := hcu
    apply hcase1 (↑u⁻¹)
    rw [← hc, mul_assoc, Units.mul_inv, mul_one]
  exfalso
  obtain ⟨⟨d, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  have hspec := IsLocalization.mk'_spec (Localization.AtPrime P) d t
  have hdP : d ∈ P := by
    by_contra hdP
    apply hcu
    have h1 : IsUnit (algebraMap A (Localization.AtPrime P) d) := by
      first
      | exact IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P) ⟨d, hdP⟩
      | exact IsLocalization.map_units (Localization.AtPrime P) (⟨d, hdP⟩ : P.primeCompl)
    rw [← hspec] at h1
    exact isUnit_of_mul_isUnit_left h1
  have had : a * d = (b : A) * t := by
    apply hK
    rw [map_mul, map_mul]
    linear_combination (algebraMap A (Localization.AtPrime P) t) * hc -
      (algebraMap A (Localization.AtPrime P) a) * hspec
  have hrad : maximalIdeal (Localization.AtPrime P) ≤
      (Ideal.span {algebraMap A (Localization.AtPrime P) (algebraMap O A ϖ)}).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro Q ⟨hJQ, hQ⟩
    have hϖQ : algebraMap A (Localization.AtPrime P) (algebraMap O A ϖ) ∈ Q :=
      hJQ (Ideal.mem_span_singleton_self _)
    haveI := hQ
    have hQ0P : Q.comap (algebraMap A (Localization.AtPrime P)) ≤ P := by
      intro x hx
      by_contra hxP
      have hu : IsUnit (algebraMap A (Localization.AtPrime P) x) := by
        first
        | exact IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P) ⟨x, hxP⟩
        | exact IsLocalization.map_units (Localization.AtPrime P) (⟨x, hxP⟩ : P.primeCompl)
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hx) hu)
    have hQ0 : Q.comap (algebraMap A (Localization.AtPrime P)) ≠ ⊥ := by
      intro h
      have h2 : algebraMap O A ϖ ∈ Q.comap (algebraMap A (Localization.AtPrime P)) :=
        Ideal.mem_comap.mpr hϖQ
      rw [h, Ideal.mem_bot] at h2
      exact hϖA0 h2
    have hQeq : Q.comap (algebraMap A (Localization.AtPrime P)) = P :=
      regVert_eq_of_le_height_one hQ0 hQ0P hP
    have hmc : Ideal.map (algebraMap A (Localization.AtPrime P))
        (Q.comap (algebraMap A (Localization.AtPrime P))) = Q := by
      first
      | exact IsLocalization.map_comap P.primeCompl (Localization.AtPrime P) Q
      | exact IsLocalization.map_comap (M := P.primeCompl) Q
    rw [hQeq] at hmc
    exact (hmaxL.trans hmc).le
  haveI hLN : IsNoetherianRing (Localization.AtPrime P) := by
    first
    | infer_instance
    | exact IsLocalization.isNoetherianRing P.primeCompl (Localization.AtPrime P) hAN
  have hfg : (maximalIdeal (Localization.AtPrime P)).FG := by
    first
    | exact IsNoetherian.noetherian _
    | exact (isNoetherianRing_iff.mp hLN).noetherian _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, maximalIdeal (Localization.AtPrime P) ^ n ≤
      Ideal.span {algebraMap A (Localization.AtPrime P) (algebraMap O A ϖ)} := by
    first
    | exact Ideal.exists_pow_le_of_le_radical_of_fg hrad hfg
    | exact Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad hfg
  have hdm : algebraMap A (Localization.AtPrime P) d ∈ maximalIdeal (Localization.AtPrime P) := by
    rw [hmaxL]
    exact Ideal.mem_map_of_mem _ hdP
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hn (Ideal.pow_mem_pow hdm n))
  obtain ⟨⟨z, u⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
  have hspec2 := IsLocalization.mk'_spec (Localization.AtPrime P) z u
  have hzu : z * algebraMap O A ϖ = d ^ n * u := by
    apply hK
    rw [map_mul, map_mul, map_pow]
    linear_combination (algebraMap A (Localization.AtPrime P) u) * hy -
      (algebraMap A (Localization.AtPrime P) (algebraMap O A ϖ)) * hspec2
  obtain ⟨s, hs_def⟩ : ∃ s : A, s = (t : A) * u := ⟨_, rfl⟩
  have hsP : s ∉ P := by
    rw [hs_def]
    exact P.primeCompl.mul_mem t.2 u.2
  have hs0 : s ≠ 0 := fun h => hsP (h ▸ P.zero_mem)
  have hpow : Submonoid.powers s ≤ nonZeroDivisors A :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hs0
  haveI hBdom : IsDomain (Localization.Away s) := by
    first
    | infer_instance
    | exact IsLocalization.isDomain_localization hpow
  haveI hBft : Algebra.FiniteType O (Localization.Away s) := by
    have h1 : Algebra.FiniteType A (Localization.Away s) := by
      haveI := IsLocalization.Away.finitePresentation (S := Localization.Away s) s
      infer_instance
    first
    | exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType O A) h1
    | infer_instance
  haveI hBfl : Module.Flat O (Localization.Away s) := by
    haveI : Module.Flat A (Localization.Away s) := by
      first
      | infer_instance
      | exact IsLocalization.flat (Localization.Away s) (Submonoid.powers s)
    first
    | exact Module.Flat.trans O A (Localization.Away s)
    | infer_instance
  have hdisj : Disjoint (Submonoid.powers s : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro x ⟨k, rfl⟩ hk
    exact hsP (Ideal.IsPrime.mem_of_pow_mem inferInstance k hk)
  haveI hPB : (P.map (algebraMap A (Localization.Away s))).IsPrime := by
    first
    | exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s)
        (Localization.Away s) P inferInstance hdisj
    | exact IsLocalization.isPrime_of_isPrime_disjoint (M := Submonoid.powers s)
        (S := Localization.Away s) P inferInstance hdisj
  have hsp : Ideal.map (algebraMap O (Localization.Away s)) (maximalIdeal O) ≠ ⊤ := by
    rw [IsScalarTower.algebraMap_eq O A (Localization.Away s), ← Ideal.map_map]
    exact ne_top_of_le_ne_top hPB.ne_top (Ideal.map_mono hv)
  have hinjB : Function.Injective (algebraMap A (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) hpow
  have he' : algebraMap A (Localization.Away s) (e * b) ≠ 0 := by
    intro h
    apply mul_ne_zero he hb0
    apply hinjB
    rw [h, map_zero]
  obtain ⟨V, indexVFirst, indexVSecond, indexVThird, indexVFourth, iV5, φ, hφ⟩ := av_point hsp _ he'
  have hφe : φ (algebraMap A (Localization.Away s) e) ≠ 0 := by
    intro h
    apply hφ
    rw [map_mul, map_mul, h, zero_mul]
  have hφb : φ (algebraMap A (Localization.Away s) b) ≠ 0 := by
    intro h
    apply hφ
    rw [map_mul, map_mul, h, mul_zero]
  obtain ⟨v, hv'⟩ :=
    hf V (φ.comp (IsScalarTower.toAlgHom O A (Localization.Away s))) a b hab' hφb hφe
  have hv2 : φ (algebraMap A (Localization.Away s) a) =
      v * φ (algebraMap A (Localization.Away s) b) := hv'
  have hsU : IsUnit (algebraMap A (Localization.Away s) s) :=
    IsLocalization.Away.algebraMap_isUnit s
  have hts : algebraMap A (Localization.Away s) s =
      algebraMap A (Localization.Away s) t * algebraMap A (Localization.Away s) u := by
    rw [← map_mul]
    exact congrArg _ hs_def
  rw [hts] at hsU
  have htU : IsUnit (φ (algebraMap A (Localization.Away s) t)) :=
    (isUnit_of_mul_isUnit_left hsU).map φ
  have huU : IsUnit (φ (algebraMap A (Localization.Away s) u)) :=
    (isUnit_of_mul_isUnit_right hsU).map φ
  have hadV := congrArg (fun x => φ (algebraMap A (Localization.Away s) x)) had
  simp only [map_mul] at hadV
  have h3 : v * φ (algebraMap A (Localization.Away s) d) =
      φ (algebraMap A (Localization.Away s) t) := by
    apply mul_left_cancel₀ hφb
    linear_combination hadV - (φ (algebraMap A (Localization.Away s) d)) * hv2
  rw [← h3] at htU
  have hdU : IsUnit (φ (algebraMap A (Localization.Away s) d)) :=
    isUnit_of_mul_isUnit_right htU
  have hzuV := congrArg (fun x => φ (algebraMap A (Localization.Away s) x)) hzu
  simp only [map_mul, map_pow] at hzuV
  have h4 : IsUnit (φ (algebraMap A (Localization.Away s) z) *
      φ (algebraMap A (Localization.Away s) (algebraMap O A ϖ))) := by
    rw [hzuV]
    exact (hdU.pow n).mul huU
  have hϖU := isUnit_of_mul_isUnit_right h4
  have hϖV : φ (algebraMap A (Localization.Away s) (algebraMap O A ϖ)) = algebraMap O V ϖ := by
    rw [← IsScalarTower.algebraMap_apply O A (Localization.Away s)]
    exact φ.commutes ϖ
  rw [hϖV] at hϖU
  haveI : Algebra.IsIntegral O V := by
    first
    | infer_instance
    | exact Algebra.IsIntegral.of_finite O V
  have hmaxV : (maximalIdeal V).comap (algebraMap O V) = maximalIdeal O := by
    haveI hmx : ((maximalIdeal V).comap (algebraMap O V)).IsMaximal := by
      first
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal V)
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) (maximalIdeal V)
      | infer_instance
      | exact Ideal.IsMaximal.under O (maximalIdeal V)
    exact IsLocalRing.eq_maximalIdeal hmx
  have hmem : ϖ ∈ (maximalIdeal V).comap (algebraMap O V) := by
    rw [hmaxV]
    exact hϖm
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp hmem)) hϖU
end Formalism.L2.Pj.RegA
