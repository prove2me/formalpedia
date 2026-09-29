-- Prove2me | solution 1 for DeligneSerre.exists_modP_eigenvector_of_complex_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e8eda6ef-5685-5518-b609-cd366d317b1c

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

open scoped Matrix

noncomputable section

private theorem funcDescent {F E : Type*} [Field F] [Field E] [Algebra F E]
    {t : ℕ} {I : Type*} (B : I → Matrix (Fin t) (Fin t) F)
    (w : Fin t → E) (j₀ : Fin t) (hw : w j₀ ≠ 0)
    (c : I → F)
    (heig : ∀ i, ((B i).map (algebraMap F E)).mulVec w = ((algebraMap F E (c i)) • w)) :
    ∃ w' : Fin t → F, w' j₀ = 1 ∧ ∀ i, (B i).mulVec w' = (c i • w') := by
  have hli : LinearIndepOn F id ({w j₀} : Set E) :=
    (linearIndepOn_singleton_iff F).mpr hw
  let Bas := Module.Basis.extend hli
  have hmem : w j₀ ∈ hli.extend (Set.subset_univ _) :=
    hli.subset_extend _ rfl
  set φ : E →ₗ[F] F := Bas.coord ⟨w j₀, hmem⟩ with hφdef
  have hφ1 : φ (w j₀) = 1 := by
    have hbase : φ (Bas ⟨w j₀, hmem⟩) = 1 := by
      simp [hφdef, Module.Basis.coord_apply, Module.Basis.repr_self]
    have hx : Bas ⟨w j₀, hmem⟩ = w j₀ := Module.Basis.extend_apply_self hli ⟨w j₀, hmem⟩
    rw [hx] at hbase
    exact hbase
  have hφsmul : ∀ (f : F) (e : E), φ (algebraMap F E f * e) = f * φ e := by
    intro f e
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  refine ⟨fun j => φ (w j), hφ1, fun i => ?_⟩
  ext j
  have hrow := congrFun (heig i) j
  have hL : (B i).mulVec (fun k => φ (w k)) j
      = φ (((B i).map (algebraMap F E)).mulVec w j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]
    congr 1
    funext k
    rw [← hφsmul]
  rw [Pi.smul_apply, smul_eq_mul, hL, hrow, Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def,
    map_smul, smul_eq_mul]

private theorem map_mulVec_comm {F E : Type*} [CommRing F] [CommRing E] (φ : F →+* E)
    {t : ℕ} (M : Matrix (Fin t) (Fin t) F) (x : Fin t → F) :
    (M.map φ).mulVec (fun j => φ (x j)) = fun j => φ (M.mulVec x j) := by
  funext j
  simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum]

private theorem descendToAlgebraic
    {t : ℕ} {I : Type*} (A : I → Matrix (Fin t) (Fin t) ℤ)
    {α : I → integralClosure ℤ ℂ} {v : Fin t → ℂ} (hv : v ≠ 0)
    (heig : ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec v = ((α i : ℂ) • v)) :
    ∃ (w : Fin t → ℂ) (j₀ : Fin t), (∀ j, IsAlgebraic ℚ (w j)) ∧ w j₀ = 1 ∧
      ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec w = ((α i : ℂ) • w) := by
  classical
  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)

  have heig' : ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec ((v j₀)⁻¹ • v)
      = ((α i : ℂ) • ((v j₀)⁻¹ • v)) := by
    intro i
    rw [Matrix.mulVec_smul, heig i, smul_comm]

  set F := algebraicClosure ℚ ℂ with hFdef
  have hmemα : ∀ i, (α i : ℂ) ∈ F :=
    fun i => mem_algebraicClosure_iff.mpr (((α i).2.isAlgebraic).extendScalars
      (R := ℤ) (S := ℚ) Int.cast_injective)
  obtain ⟨w', hw'1, heigw'⟩ := funcDescent (F := F) (E := ℂ)
    (fun i => (A i).map (Int.cast : ℤ → F))
    ((v j₀)⁻¹ • v) j₀ (by simp [Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hj₀])
    (fun i => ⟨(α i : ℂ), hmemα i⟩)
    (by
      intro i
      have hmm : ((A i).map (Int.cast : ℤ → F)).map (algebraMap F ℂ)
          = (A i).map (Int.cast : ℤ → ℂ) := by
        rw [Matrix.map_map]
        congr 1
      rw [hmm]
      exact heig' i)
  have hmm : ∀ i, ((A i).map (Int.cast : ℤ → F)).map (algebraMap F ℂ)
      = (A i).map (Int.cast : ℤ → ℂ) := by
    intro i
    rw [Matrix.map_map]
    congr 1
  refine ⟨fun j => (w' j : ℂ), j₀, fun j => mem_algebraicClosure_iff.mp (w' j).2, by
    show ((w' j₀ : F) : ℂ) = 1
    rw [hw'1]
    simp, fun i => ?_⟩
  funext j
  have hcoord := congrFun (map_mulVec_comm (algebraMap F ℂ)
    ((A i).map (Int.cast : ℤ → F)) w') j
  have hstep : ((A i).map (Int.cast : ℤ → ℂ)).mulVec (fun k => (w' k : ℂ)) j
      = ((((A i).map (Int.cast : ℤ → F)).mulVec w') j : ℂ) := by
    rw [← hmm i]
    exact hcoord
  rw [Pi.smul_apply, smul_eq_mul, hstep, congrFun (heigw' i) j]
  simp [Pi.smul_apply, smul_eq_mul]

private theorem reduceAlgebraicEigenvector
    {t : ℕ} {I : Type*} (A : I → Matrix (Fin t) (Fin t) ℤ)
    {p : ℕ} [Fact p.Prime]
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (hmax : 𝔪.IsPrime)
    (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    {α : I → integralClosure ℤ ℂ}
    (w : Fin t → ℂ) (j₀ : Fin t) (halg : ∀ j, IsAlgebraic ℚ (w j)) (hw : w j₀ = 1)
    (heig : ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec w = ((α i : ℂ) • w))
    {n : I → ℤ} (hcong : ∀ i, α i - (n i : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∃ m : Fin t → ZMod p, m ≠ 0 ∧
      ∀ i, ((A i).map (Int.cast : ℤ → ZMod p)).mulVec m = ((n i : ZMod p) • m) := by
  classical

  set L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range w) with hLdef
  have hwmem : ∀ j, w j ∈ L := fun j =>
    IntermediateField.subset_adjoin ℚ _ ⟨j, rfl⟩
  have hLfd : FiniteDimensional ℚ L := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x ⟨j, rfl⟩
    exact (halg j).isIntegral

  have hαmem : ∀ i, (α i : ℂ) ∈ L := by
    intro i
    have hrow := congrFun (heig i) j₀
    have : (α i : ℂ) = ((A i).map (Int.cast : ℤ → ℂ)).mulVec w j₀ := by
      rw [hrow, Pi.smul_apply, smul_eq_mul, hw, mul_one]
    rw [this]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact sum_mem fun k _ =>
      mul_mem (by exact_mod_cast IntermediateField.intCast_mem L _) (hwmem k)

  haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  haveI hZQ : Algebra.IsAlgebraic ℤ ℚ := by
    constructor
    intro x
    refine ⟨Polynomial.C (x.den : ℤ) * Polynomial.X - Polynomial.C x.num, ?_, ?_⟩
    · intro h
      have h1 := congrArg (fun q => Polynomial.coeff q 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
        Polynomial.coeff_C, mul_one, Polynomial.coeff_zero] at h1
      rw [if_neg (by norm_num : ¬ (1 : ℕ) = 0), sub_zero] at h1
      exact (Int.natCast_ne_zero.mpr x.den_ne_zero) h1
    · have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      simp only [map_sub, map_mul, Polynomial.aeval_X, map_intCast,
        map_natCast, eq_intCast]
      rw [sub_eq_zero, mul_comm, ← eq_div_iff hd]
      exact_mod_cast (Rat.num_div_den x).symm
  haveI : Algebra.IsAlgebraic ℤ L :=
    ⟨fun x => (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).restrictScalars (R := ℤ)⟩
  obtain ⟨d, hd0, hdint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ
    (Finset.univ.image (fun j => (⟨w j, hwmem j⟩ : L)))

  set 𝓞 := integralClosure ℤ L with h𝓞def
  have hxint : ∀ j, IsIntegral ℤ (d • (⟨w j, hwmem j⟩ : L)) := fun j =>
    hdint _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))
  set x : Fin t → 𝓞 := fun j => ⟨d • (⟨w j, hwmem j⟩ : L), hxint j⟩ with hxdef
  have hxj₀ : (x j₀ : L) = (d : L) := by
    simp only [hxdef]
    have : (⟨w j₀, hwmem j₀⟩ : L) = 1 := by
      ext
      exact hw
    simp [this, zsmul_eq_mul]

  have hαintL : ∀ i, IsIntegral ℤ (⟨(α i : ℂ), hαmem i⟩ : L) := fun i =>
    (isIntegral_algebraMap_iff (algebraMap L ℂ).injective).mp (α i).2
  set c : I → 𝓞 := fun i => ⟨⟨(α i : ℂ), hαmem i⟩, hαintL i⟩ with hcdef
  set iotaC : 𝓞 →+* ℂ := (algebraMap L ℂ).comp (algebraMap 𝓞 L) with hICdef
  have hICinj : Function.Injective iotaC := by
    intro a b hab
    have h1 : (a : L) = (b : L) := (algebraMap L ℂ).injective hab
    exact Subtype.ext h1
  have hICx : ∀ j, iotaC (x j) = d • w j := by
    intro j
    simp only [hICdef, hxdef, RingHom.coe_comp, Function.comp_apply]
    have : (algebraMap 𝓞 L) (⟨d • (⟨w j, hwmem j⟩ : L), hxint j⟩ : 𝓞)
        = d • (⟨w j, hwmem j⟩ : L) := rfl
    rw [this, map_zsmul]
    congr 1
  have hICc : ∀ i, iotaC (c i) = (α i : ℂ) := fun i => rfl
  have heig𝓞 : ∀ i, ((A i).map (Int.cast : ℤ → 𝓞)).mulVec x = (fun k => c i * x k) := by
    intro i
    funext j
    apply hICinj
    have hpush := congrFun (map_mulVec_comm iotaC ((A i).map (Int.cast : ℤ → 𝓞)) x) j
    have hmm𝓞 : ((A i).map (Int.cast : ℤ → 𝓞)).map iotaC = (A i).map (Int.cast : ℤ → ℂ) := by
      rw [Matrix.map_map]
      congr 1

    have hL : iotaC (((A i).map (Int.cast : ℤ → 𝓞)).mulVec x j)
        = ((A i).map (Int.cast : ℤ → ℂ)).mulVec (fun k => iotaC (x k)) j := by
      rw [← hmm𝓞]
      exact hpush.symm
    rw [hL]

    have hxw : (fun k => iotaC (x k)) = fun k => (d : ℂ) * w k := by
      funext k
      rw [hICx k, zsmul_eq_mul]
    rw [hxw]
    have hsc : ((A i).map (Int.cast : ℤ → ℂ)).mulVec (fun k => (d : ℂ) * w k) j
        = (d : ℂ) * (((A i).map (Int.cast : ℤ → ℂ)).mulVec w j) := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
      congr 1
      funext k
      ring
    rw [hsc, congrFun (heig i) j]

    have : iotaC (c i * x j) = (α i : ℂ) * ((d : ℂ) * w j) := by
      rw [map_mul, hICc, hICx, zsmul_eq_mul]
    rw [this, Pi.smul_apply, smul_eq_mul]
    ring

  have hmapint : ∀ o : 𝓞, IsIntegral ℤ (iotaC o) := by
    intro o
    have := o.2
    exact (isIntegral_algebraMap_iff (algebraMap L ℂ).injective).mpr o.2
  set ι : 𝓞 →+* integralClosure ℤ ℂ :=
    { toFun := fun o => ⟨iotaC o, hmapint o⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp } with hιdef
  set 𝔭 : Ideal 𝓞 := Ideal.comap ι 𝔪 with h𝔭def
  haveI h𝔭prime : 𝔭.IsPrime := Ideal.IsPrime.comap ι (hK := hmax)
  have hp𝔭 : (p : 𝓞) ∈ 𝔭 := by
    have : ι (p : 𝓞) = (p : integralClosure ℤ ℂ) := by
      ext
      simp [hιdef]
    simp only [h𝔭def, Ideal.mem_comap, this]
    exact hp𝔪
  have hcong𝔭 : ∀ i, c i - (n i : 𝓞) ∈ 𝔭 := by
    intro i
    have : ι (c i - (n i : 𝓞)) = α i - (n i : integralClosure ℤ ℂ) := by
      ext
      simp [hιdef, hICc]
    simp only [h𝔭def, Ideal.mem_comap, this]
    exact hcong i

  haveI hLnf : NumberField L := @NumberField.mk L _ inferInstance hLfd
  haveI hDD : IsDedekindDomain 𝓞 := integralClosure.isDedekindDomain (A := ℤ) (K := ℚ) (L := L)
  have h𝔭ne : 𝔭 ≠ ⊥ := by
    intro hbot
    have hp0 : (p : 𝓞) = 0 := by
      rw [← Ideal.mem_bot, ← hbot]
      exact hp𝔭
    have : (p : ℂ) = 0 := by
      have := congrArg iotaC hp0
      simpa [map_natCast] using this
    exact (Nat.cast_ne_zero (R := ℂ)).mpr (Fact.out : p.Prime).ne_zero this
  haveI hODVR : IsDiscreteValuationRing (Localization.AtPrime 𝔭) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain 𝓞 h𝔭ne (Localization.AtPrime 𝔭)
  have hOinj : Function.Injective (algebraMap 𝓞 (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective (Localization.AtPrime 𝔭) 𝔭.primeCompl_le_nonZeroDivisors

  set y : Fin t → (Localization.AtPrime 𝔭) := fun j => algebraMap 𝓞 (Localization.AtPrime 𝔭) (x j) with hydef
  have hyj₀ : y j₀ ≠ 0 := by
    simp only [hydef]
    intro h0
    have := hOinj (h0.trans (map_zero _).symm)
    apply hd0
    have hxz := congrArg (fun o : 𝓞 => (o : L)) this
    simp only [hxj₀] at hxz
    exact_mod_cast hxz
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔭)
  have hJne : Ideal.span (Set.range y) ≠ ⊥ := by
    intro hJ
    exact hyj₀ ((Ideal.span_eq_bot.mp hJ) _ ⟨j₀, rfl⟩)
  obtain ⟨e, hJ⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hJne hϖ
  have hymem : ∀ j, ∃ zz : (Localization.AtPrime 𝔭), y j = ϖ ^ e * zz := by
    intro j
    have : y j ∈ Ideal.span (Set.range y) := Ideal.subset_span ⟨j, rfl⟩
    rw [hJ, Ideal.mem_span_singleton] at this
    obtain ⟨zz, hzz⟩ := this
    exact ⟨zz, hzz⟩
  choose z hz using hymem
  have hϖe0 : ϖ ^ e ≠ 0 := pow_ne_zero _ hϖ.ne_zero

  have hzunit : ∃ j₁, IsUnit (z j₁) := by
    by_contra hnone
    push Not at hnone
    have hJle : Ideal.span (Set.range y) ≤ Ideal.span {ϖ ^ (e + 1)} := by
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_span_singleton, hz j, pow_succ]
      have hzj : ϖ ∣ z j := by
        have hm : z j ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) :=
          (IsLocalRing.mem_maximalIdeal _).mpr (hnone j)
        rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
      exact mul_dvd_mul_left _ hzj
    have hdvd : ϖ ^ (e + 1) ∣ ϖ ^ e := by
      rw [← Ideal.mem_span_singleton]
      exact hJle (hJ ▸ Ideal.subset_span (Set.mem_singleton _))
    obtain ⟨k, hk⟩ := hdvd
    rw [pow_succ, mul_assoc] at hk
    have h1 : (1 : (Localization.AtPrime 𝔭)) = ϖ * k :=
      mul_left_cancel₀ hϖe0 (by rw [mul_one]; exact hk)
    exact hϖ.not_isUnit (isUnit_iff_exists_inv.mpr ⟨k, h1.symm⟩)
  obtain ⟨j₁, hj₁⟩ := hzunit

  have heigO : ∀ i, ((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))).mulVec z
      = (fun k => algebraMap 𝓞 (Localization.AtPrime 𝔭) (c i) * z k) := by
    intro i
    funext j
    have hO := congrArg (algebraMap 𝓞 (Localization.AtPrime 𝔭)) (congrFun (heig𝓞 i) j)
    have hpushO := congrFun (map_mulVec_comm (algebraMap 𝓞 (Localization.AtPrime 𝔭))
      ((A i).map (Int.cast : ℤ → 𝓞)) x) j
    have hmmO : ((A i).map (Int.cast : ℤ → 𝓞)).map (algebraMap 𝓞 (Localization.AtPrime 𝔭))
        = (A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭)) := by
      rw [Matrix.map_map]
      congr 1
      funext zz
      simp

    have heigY : ((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))).mulVec y j
        = algebraMap 𝓞 (Localization.AtPrime 𝔭) (c i) * y j := by
      have h1 : ((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))).mulVec y j
          = algebraMap 𝓞 (Localization.AtPrime 𝔭) (((A i).map (Int.cast : ℤ → 𝓞)).mulVec x j) := by
        rw [← hmmO]
        exact hpushO
      rw [h1, congrFun (heig𝓞 i) j, map_mul]

    have hyz : y = fun k => ϖ ^ e * z k := funext hz
    rw [hyz] at heigY
    have hsc : ((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))).mulVec (fun k => ϖ ^ e * z k) j
        = ϖ ^ e * (((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))).mulVec z j) := by
      simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
      congr 1
      funext k
      ring
    rw [hsc] at heigY
    apply mul_left_cancel₀ hϖe0
    rw [heigY]
    ring

  have hmemmax : ∀ o : 𝓞, o ∈ 𝔭 → algebraMap 𝓞 (Localization.AtPrime 𝔭) o ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by
    intro o ho
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 o]
    exact ho
  have hpκ : ((p : ℕ) : IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) = 0 := by
    have h1 : (p : (Localization.AtPrime 𝔭)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by
      have := hmemmax ((p : ℕ) : 𝓞) hp𝔭
      rwa [map_natCast] at this
    have h2 : ((p : ℕ) : IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) = IsLocalRing.residue (Localization.AtPrime 𝔭) ((p : ℕ) : (Localization.AtPrime 𝔭)) := by
      rw [map_natCast]
    rw [h2]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr h1
  haveI hκp : CharP (IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) p := by
    have hdvd : ringChar (IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) ∣ p := ringChar.dvd hpκ
    have hne1 : ringChar (IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) ≠ 1 := by
      intro h1
      have := CharP.cast_eq_zero (IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) (ringChar (IsLocalRing.ResidueField (Localization.AtPrime 𝔭)))
      rw [h1] at this
      exact one_ne_zero (by exact_mod_cast this)
    have hrc := ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd).resolve_left hne1
    rw [← hrc]
    exact ringChar.charP _
  letI : Algebra (ZMod p) (IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) := ZMod.algebra _ p
  set zbar : Fin t → IsLocalRing.ResidueField (Localization.AtPrime 𝔭) := fun j => IsLocalRing.residue (Localization.AtPrime 𝔭) (z j) with hzbardef
  have hzbar₁ : zbar j₁ ≠ 0 := by
    simp only [hzbardef]
    intro h0
    have hmem := (IsLocalRing.residue_eq_zero_iff _).mp h0
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem hj₁

  have hcn : ∀ i, IsLocalRing.residue (Localization.AtPrime 𝔭) (algebraMap 𝓞 (Localization.AtPrime 𝔭) (c i)) = ((n i : ℤ) : IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) := by
    intro i
    have hdiff : algebraMap 𝓞 (Localization.AtPrime 𝔭) (c i) - ((n i : ℤ) : (Localization.AtPrime 𝔭)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by
      have := hmemmax (c i - (n i : 𝓞)) (hcong𝔭 i)
      rwa [map_sub, map_intCast] at this
    have := (IsLocalRing.residue_eq_zero_iff _).mpr hdiff
    rw [map_sub, map_intCast, sub_eq_zero] at this
    exact this
  have heigκ : ∀ i, ((A i).map (Int.cast : ℤ → IsLocalRing.ResidueField (Localization.AtPrime 𝔭))).mulVec zbar
      = fun k => ((n i : ℤ) : IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) * zbar k := by
    intro i
    funext j
    have hpushρ := congrFun (map_mulVec_comm (IsLocalRing.residue (Localization.AtPrime 𝔭))
      ((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))) z) j
    have hmmρ : ((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))).map (IsLocalRing.residue (Localization.AtPrime 𝔭))
        = (A i).map (Int.cast : ℤ → IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) := by
      rw [Matrix.map_map]
      congr 1
    have hred := congrArg (IsLocalRing.residue (Localization.AtPrime 𝔭)) (congrFun (heigO i) j)
    rw [map_mul, hcn] at hred
    calc ((A i).map (Int.cast : ℤ → IsLocalRing.ResidueField (Localization.AtPrime 𝔭))).mulVec zbar j
        = IsLocalRing.residue (Localization.AtPrime 𝔭) (((A i).map (Int.cast : ℤ → (Localization.AtPrime 𝔭))).mulVec z j) := by
          rw [← hmmρ]
          exact hpushρ
      _ = ((n i : ℤ) : IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) * zbar j := hred

  obtain ⟨m, hm1, heigm⟩ := funcDescent (F := ZMod p) (E := IsLocalRing.ResidueField (Localization.AtPrime 𝔭))
    (fun i => (A i).map (Int.cast : ℤ → ZMod p)) zbar j₁ hzbar₁
    (fun i => ((n i : ℤ) : ZMod p))
    (by
      intro i
      have hmmZ : (((A i).map (Int.cast : ℤ → ZMod p)).map
          (algebraMap (ZMod p) (IsLocalRing.ResidueField (Localization.AtPrime 𝔭))))
          = (A i).map (Int.cast : ℤ → IsLocalRing.ResidueField (Localization.AtPrime 𝔭)) := by
        rw [Matrix.map_map]
        congr 1
        funext zz
        simp
      rw [hmmZ, heigκ i]
      funext k
      rw [Pi.smul_apply, smul_eq_mul, map_intCast])
  refine ⟨m, ?_, fun i => ?_⟩
  · intro h0
    rw [h0] at hm1
    exact one_ne_zero hm1.symm
  · rw [heigm i]

theorem solution
    {t : ℕ} {I : Type*} (A : I → Matrix (Fin t) (Fin t) ℤ)
    {p : ℕ} [Fact p.Prime]
    {𝔪 : Ideal (integralClosure ℤ ℂ)} (hmax : 𝔪.IsPrime)
    (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    {α : I → integralClosure ℤ ℂ} {v : Fin t → ℂ} (hv : v ≠ 0)
    (heig : ∀ i, ((A i).map (Int.cast : ℤ → ℂ)).mulVec v = ((α i : ℂ) • v))
    {n : I → ℤ} (hcong : ∀ i, α i - (n i : integralClosure ℤ ℂ) ∈ 𝔪) :
    ∃ m : Fin t → ZMod p, m ≠ 0 ∧
      ∀ i, ((A i).map (Int.cast : ℤ → ZMod p)).mulVec m = ((n i : ZMod p) • m) := by
  obtain ⟨w, j₀, halg, hw1, heigw⟩ := descendToAlgebraic A hv heig
  exact reduceAlgebraicEigenvector A hmax hp𝔪 w j₀ halg hw1 heigw hcong

end
end S_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector
end P2MW
export P2MW.S_DeligneSerre_exists_modP_eigenvector_of_complex_eigenvector (solution)
