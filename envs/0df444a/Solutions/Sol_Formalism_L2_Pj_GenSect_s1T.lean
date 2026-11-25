-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.s1T
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:31:43.364367+00:00
-- url     : https://prove2.me/submissions/3c215a0b-0ada-40c6-9601-11c035049fb8

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSect
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectT
import Theorems.Thm_Formalism_L2_Pj_GenSect_s1


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω Kl K' : Type) [Field K] [Field Ω] [Algebra K Ω] [Field Kl] [Field K'] [Algebra K Kl]
  [Algebra Kl K'] [Algebra K K'] [IsScalarTower K Kl K']
variable {K Ω Kl K'} {D m : ℕ}
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (v : Fin m → Ω) (k₀ : Fin m) (hv₀ : v k₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun k => v k / v k₀)) = D)
    (t : Fin (D + 1) × Fin m → K') (ht : AlgebraicIndependent K t) :
    FiniteDimensional K' (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) ∧
      IsReduced (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) := by
  classical

  have hφ : Function.Injective (MvPolynomial.aeval t : KT K D m →ₐ[K] K').toRingHom := ht
  letI : Algebra (KTf K D m) K' := (IsFractionRing.lift (A := KT K D m) (K := KTf K D m) hφ).toAlgebra
  obtain ⟨-, hB⟩ := s1 (K := K) hfg htr v k₀ hv₀ hbig
  obtain ⟨hBfin, hBred⟩ := hB K'
  let ι : TZ K Ω Kl K' →+* (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) :=
    algebraMap (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v)
  have hιK : ∀ z : K', ι (algebraMap K' (TZ K Ω Kl K') z) =
      algebraMap K' (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) z := fun z =>
    (IsScalarTower.algebraMap_apply K' (TZ K Ω Kl K') _ z).symm

  let fΩ : Ω →+* TZ K Ω Kl K' :=
    (Algebra.TensorProduct.includeRight (R := Kl) (A := K')).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := K) (A := Kl)).toRingHom
  let e0 : ΩT Ω D m →+* TZ K Ω Kl K' :=
    MvPolynomial.eval₂Hom fΩ (fun p => t p ⊗ₜ[Kl] (1 : Kl ⊗[K] Ω))
  have hKΩ : ∀ a : K, fΩ (algebraMap K Ω a) = algebraMap K' (TZ K Ω Kl K') (algebraMap K K' a) := by
    intro a
    show (1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] algebraMap K Ω a) = _
    rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]
    have h1 : (algebraMap K Kl a ⊗ₜ[K] (1 : Ω) : Kl ⊗[K] Ω) = algebraMap K Kl a • (1 : Kl ⊗[K] Ω) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.one_def]
    rfl
  have he0kt : ∀ q : KT K D m, e0 (ktToΩ K Ω D m q) =
      algebraMap K' (TZ K Ω Kl K') (MvPolynomial.aeval t q) := by
    intro q
    have : e0.comp (ktToΩ K Ω D m) =
        (algebraMap K' (TZ K Ω Kl K')).comp (MvPolynomial.aeval t : KT K D m →ₐ[K] K').toRingHom := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun p => ?_)
      · simp only [RingHom.comp_apply, ktToΩ, MvPolynomial.map_C, e0, MvPolynomial.eval₂Hom_C,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C]
        exact hKΩ a
      · simp only [RingHom.comp_apply, ktToΩ, MvPolynomial.map_X, e0, MvPolynomial.eval₂Hom_X',
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
        rfl
    exact congrArg (fun f => f q) this
  have he0sec : ∀ i : Fin D, e0 (sec v i) = tsec K Kl t v i.succ := by
    intro i
    simp only [sec, tsec, map_sum, map_mul, e0, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (t (i.succ, k) ⊗ₜ[Kl] (1 : Kl ⊗[K] Ω)) * ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] v k)) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

  let g0 : RS K Ω D m →+* (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) :=
    IsLocalization.lift (M := KTS K Ω D m) (g := ι.comp e0) (by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, rfl⟩ := hs
      show IsUnit (ι (e0 (ktToΩ K Ω D m q)))
      rw [he0kt]
      have hne : (MvPolynomial.aeval t : KT K D m →ₐ[K] K') q ≠ 0 := fun h =>
        nonZeroDivisors.ne_zero hq (hφ (h.trans (map_zero _).symm))
      exact (IsUnit.mk0 _ hne).map (ι.comp (algebraMap K' (TZ K Ω Kl K'))))
  have hg0 : ∀ a : ΩT Ω D m, g0 (algebraMap (ΩT Ω D m) (RS K Ω D m) a) = ι (e0 a) := fun a =>
    IsLocalization.lift_eq _ a
  have hmemJ : ∀ i : Fin D, ι (tsec K Kl t v i.succ) = 0 := by
    intro i
    rw [IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0))
      (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v)]
    rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    have h1 : algebraMap (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0)) (tsec K Kl t v i.succ) =
        algebraMap (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0)) (tsec K Kl t v 0) *
          (algebraMap (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0)) (tsec K Kl t v i.succ) *
            IsLocalization.Away.invSelf (tsec K Kl t v 0)) := by
      rw [mul_left_comm, IsLocalization.Away.mul_invSelf, mul_one]
    rw [h1]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have hIs : ∀ a ∈ Is K v, g0 a = 0 := by
    intro a ha
    have hle : Is K v ≤ RingHom.ker g0 := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, hg0, he0sec, hmemJ]
    exact hle ha
  let g1 : (RS K Ω D m ⧸ Is K v) →+* (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) :=
    Ideal.Quotient.lift (Is K v) g0 hIs
  have hcomm : g1.comp (algebraMap (KTf K D m) (RS K Ω D m ⧸ Is K v)) =
      algebraMap (KTf K D m) (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (KT K D m)) (RingHom.ext fun q => ?_)
    simp only [RingHom.comp_apply]
    rw [← Ideal.Quotient.mk_algebraMap]
    have hmap : algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
        algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := IsLocalization.map_eq _ _
    rw [hmap]
    show g0 _ = _
    rw [hg0, he0kt, hιK]
    rw [IsScalarTower.algebraMap_apply (KTf K D m) K' (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v)]
    rw [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
    rfl
  let g : (RS K Ω D m ⧸ Is K v) →ₐ[KTf K D m] (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) :=
    { g1 with commutes' := fun r => congrArg (fun f => f r) hcomm }
  let Θ := Algebra.TensorProduct.lift (Algebra.ofId K' (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v))
    g (fun _ _ => Commute.all _ _)
  haveI : IsArtinianRing (K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K v)) :=
    IsArtinianRing.of_finite K' _

  have hΘ1 : ∀ y : RS K Ω D m ⧸ Is K v, Θ (1 ⊗ₜ y) = g y := fun y => by
    simp [Θ, Algebra.TensorProduct.lift_tmul]
  have hι : ∀ z : TZ K Ω Kl K', ι z ∈ Θ.range := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul k y =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add]; exact add_mem ha hb
      | tmul l ω =>
        have he : k ⊗ₜ[Kl] (l ⊗ₜ[K] ω) =
            algebraMap K' (TZ K Ω Kl K') (k * algebraMap Kl K' l) * fΩ ω := by
          show _ = ((k * algebraMap Kl K' l) ⊗ₜ[Kl] (1 : Kl ⊗[K] Ω)) * ((1 : K') ⊗ₜ[Kl] ((1 : Kl) ⊗ₜ[K] ω))
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
          have : l ⊗ₜ[K] ω = l • ((1 : Kl) ⊗ₜ[K] ω) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm]
        rw [he, map_mul]
        refine mul_mem ?_ ?_
        · rw [hιK]; exact Subalgebra.algebraMap_mem _ _
        · have : ι (fΩ ω) = Θ (1 ⊗ₜ (Ideal.Quotient.mk (Is K v)
              (algebraMap (ΩT Ω D m) (RS K Ω D m) (MvPolynomial.C ω)))) := by
            rw [hΘ1]
            show _ = g0 _
            rw [hg0]
            simp [e0]
          rw [this]; exact Θ.mem_range_self _
  have hu : IsUnit (ι (tsec K Kl t v 0)) := by
    rw [IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0))
      (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v)]
    exact (IsLocalization.Away.algebraMap_isUnit (tsec K Kl t v 0)).map _
  obtain ⟨b0, hb0'⟩ := hι (tsec K Kl t v 0)
  have hb0 : Θ b0 = ι (tsec K Kl t v 0) := hb0'
  obtain ⟨n0, y0, hy0⟩ := IsArtinian.exists_pow_succ_smul_dvd b0 (1 : K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K v))
  have hinv : ι (tsec K Kl t v 0) * Θ y0 = 1 := by
    rw [Nat.succ_eq_add_one, smul_eq_mul, smul_eq_mul, mul_one] at hy0
    have h := congrArg Θ hy0
    rw [map_mul, map_pow, map_pow, hb0] at h
    have h' : ι (tsec K Kl t v 0) ^ n0 * (ι (tsec K Kl t v 0) * Θ y0) = ι (tsec K Kl t v 0) ^ n0 * 1 := by
      rw [← mul_assoc, ← pow_succ, h, mul_one]
    exact (hu.pow n0).mul_left_cancel h'
  have hsurj : Function.Surjective Θ := by
    intro c
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨⟨z, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (tsec K Kl t v 0)) w
    obtain ⟨n, hn'⟩ := s.2
    have hn : tsec K Kl t v 0 ^ n = (s : TZ K Ω Kl K') := hn'
    have hcs : Ideal.Quotient.mk (tJ K Kl t v)
        (IsLocalization.mk' (Localization.Away (tsec K Kl t v 0)) z s) * ι (tsec K Kl t v 0) ^ n = ι z := by
      rw [IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0))
        (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v),
        IsScalarTower.algebraMap_apply (TZ K Ω Kl K') (Localization.Away (tsec K Kl t v 0))
        (Localization.Away (tsec K Kl t v 0) ⧸ tJ K Kl t v) z]
      rw [Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_pow, ← map_mul, hn, IsLocalization.mk'_spec]
    have hc : Ideal.Quotient.mk (tJ K Kl t v)
        (IsLocalization.mk' (Localization.Away (tsec K Kl t v 0)) z s) = ι z * Θ y0 ^ n := by
      rw [← hcs, mul_assoc, ← mul_pow, hinv, one_pow, mul_one]
    have hm : ι z * Θ y0 ^ n ∈ Θ.range := mul_mem (hι z) (pow_mem (Θ.mem_range_self y0) n)
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, by rw [hc]; exact hb⟩
  refine ⟨Module.Finite.of_surjective Θ.toLinearMap hsurj, ?_⟩

  have hvnrB : ∀ b : K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K v), ∃ y, b = b ^ 2 * y := by
    intro b
    obtain ⟨n, y, h⟩ := IsArtinian.exists_pow_succ_smul_dvd b (1 : K' ⊗[KTf K D m] (RS K Ω D m ⧸ Is K v))
    rw [Nat.succ_eq_add_one, smul_eq_mul, smul_eq_mul, mul_one] at h
    have hnil : IsNilpotent (b * (1 - b * y)) := by
      refine ⟨n + 1, ?_⟩
      rw [mul_pow]
      linear_combination (-(b * (1 - b * y) ^ n)) * h
    have h0 := hBred.eq_zero _ hnil
    exact ⟨y, by linear_combination h0⟩
  refine ⟨fun c hc => ?_⟩
  obtain ⟨k, hk⟩ := hc
  obtain ⟨b, rfl⟩ := hsurj c
  obtain ⟨y, hy⟩ := hvnrB b
  have hv : Θ b = Θ b ^ 2 * Θ y := by rw [← map_pow, ← map_mul, ← hy]
  have hpow : ∀ j : ℕ, Θ b = Θ b ^ (j + 1) * Θ y ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc Θ b = Θ b ^ (j + 1) * Θ y ^ j := ih
        _ = Θ b ^ j * Θ b * Θ y ^ j := by rw [pow_succ]
        _ = Θ b ^ j * (Θ b ^ 2 * Θ y) * Θ y ^ j := by rw [← hv]
        _ = Θ b ^ (j + 1 + 1) * Θ y ^ (j + 1) := by ring
  rw [hpow k, pow_succ, hk, zero_mul, zero_mul]
end Formalism.L2.Pj.GenSect
