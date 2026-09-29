-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/0d29c75a-ff7a-516b-ba38-e3a60d9ffd55

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal MvPowerSeries MvFormalGroup
open scoped Quaternion

universe u v w

noncomputable section

namespace D2aExtension

section Engine

variable {R : Type u} [CommRing R] {C : Type v} [CommRing C] [Algebra R C] {σ : Type w}

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem prod_pow_mem_pow_degree (I : Ideal C) {x : σ → C} (hx : ∀ s, x s ∈ I) (d : σ →₀ ℕ) :
    (d.prod fun s e => x s ^ e) ∈ I ^ d.degree := by
  rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hx s) _

theorem prod_pow_eq_zero_of_le_degree (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (d : σ →₀ ℕ) (hd : N ≤ d.degree) :
    (d.prod fun s e => x s ^ e) = 0 := by
  have := (Ideal.pow_le_pow_right hd) (prod_pow_mem_pow_degree J hx d)
  rwa [hN, Submodule.mem_bot] at this

theorem adicEval_eq_sum [Finite σ] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∉ D → N ≤ d.degree) :
    MvFormalGroup.adicEval J x f = ∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal C := ⟨J⟩
  haveI hc : IsAdicComplete J C := isAdicComplete_of_isNilpotent J ⟨N, hN⟩
  haveI : CompleteSpace C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).1
  haveI : T2Space C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).2
  have hφ : Continuous (algebraMap R C) := continuous_of_discreteTopology
  have ha : MvPowerSeries.HasEval x := by
    refine ⟨fun s => ?_, ?_⟩
    · apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      have h0 : x s ^ n = 0 := by
        have hmem : x s ^ n ∈ J ^ n := Ideal.pow_mem_pow (hx s) n
        have := (Ideal.pow_le_pow_right hn) hmem
        rwa [hN, Submodule.mem_bot] at this
      exact h0
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  have h1 := MvPowerSeries.hasSum_eval₂ hφ ha f
  have h2 : HasSum (fun d : σ →₀ ℕ => algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e)
      (∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e) := by
    apply hasSum_sum_of_ne_finset_zero
    intro d hd'
    rw [prod_pow_eq_zero_of_le_degree J hN hx d (hD d hd'), mul_zero]
  exact h1.unique h2

theorem le_degree_of_not_mem_Iic [Fintype σ] [DecidableEq σ] (N : ℕ) (d : σ →₀ ℕ)
    (hd : d ∉ Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => N)) : N ≤ d.degree := by
  classical
  rw [Finset.mem_Iic] at hd
  have : ∃ s, N < d s := by
    by_contra h
    push Not at h
    exact hd fun s => by simpa using h s
  obtain ⟨s, hs⟩ := this
  calc N ≤ d s := hs.le
    _ ≤ d.degree := by
        rw [Finsupp.degree_apply]
        by_cases hs0 : s ∈ d.support
        · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs0
        · rw [Finsupp.notMem_support_iff.mp hs0]; exact Nat.zero_le _

theorem exists_pow_eq_bot {J : Ideal C} (hJ : IsNilpotent J) : ∃ n : ℕ, J ^ n = ⊥ := hJ

theorem adicEval_mem_pow [Finite σ] (J : Ideal C) (hJ : IsNilpotent J) (I : Ideal C) (hIJ : I ≤ J) {x : σ → C}
    (hx : ∀ s, x s ∈ I) (n₀ : ℕ) {f : MvPowerSeries σ R} (hf : ∀ d : σ →₀ ℕ, d.degree < n₀ → coeff d f = 0) :
    MvFormalGroup.adicEval J x f ∈ I ^ n₀ := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  replace hN : J ^ N = ⊥ := hN
  rw [adicEval_eq_sum J hN (fun s => hIJ (hx s)) f _ (le_degree_of_not_mem_Iic N)]
  refine Ideal.sum_mem _ fun d _ => ?_
  by_cases hd : d.degree < n₀
  · rw [hf d hd, map_zero, zero_mul]
    exact Submodule.zero_mem _
  · push Not at hd
    exact Ideal.mul_mem_left _ _ ((Ideal.pow_le_pow_right hd) (prod_pow_mem_pow_degree I hx d))

theorem adicEval_mem' [Finite σ] (J : Ideal C) (hJ : IsNilpotent J) (I : Ideal C) (hIJ : I ≤ J) {x : σ → C}
    (hx : ∀ s, x s ∈ I) {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) : MvFormalGroup.adicEval J x f ∈ I := by
  have h := adicEval_mem_pow J hJ I hIJ hx 1 (f := f) (fun d hd => by
    have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst hd0
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply])
  rwa [pow_one] at h

theorem adicEval_mem [Finite σ] (J : Ideal C) (hJ : IsNilpotent J) {x : σ → C}
    (hx : ∀ s, x s ∈ J) {f : MvPowerSeries σ R} (hf : f.constantCoeff = 0) : MvFormalGroup.adicEval J x f ∈ J :=
  adicEval_mem' J hJ J le_rfl hx hf

theorem map_adicEval [Finite σ] {C' : Type v} [CommRing C'] [Algebra R C'] (J : Ideal C) (hJ : IsNilpotent J)
    (J' : Ideal C') (hJ' : IsNilpotent J') (φ : C →ₐ[R] C') (hφ : ∀ s ∈ J, φ s ∈ J')
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) :
    φ (MvFormalGroup.adicEval J x f) = MvFormalGroup.adicEval J' (φ ∘ x) f := by
  classical
  haveI := Fintype.ofFinite σ
  obtain ⟨N, hN⟩ := hJ
  obtain ⟨N', hN'⟩ := hJ'
  replace hN : J ^ N = ⊥ := hN
  replace hN' : J' ^ N' = ⊥ := hN'
  have hM : J ^ (max N N') = ⊥ := le_bot_iff.1 ((Ideal.pow_le_pow_right (le_max_left N N')).trans hN.le)
  have hM' : J' ^ (max N N') = ⊥ := le_bot_iff.1 ((Ideal.pow_le_pow_right (le_max_right N N')).trans hN'.le)
  rw [adicEval_eq_sum J hM hx f _ (le_degree_of_not_mem_Iic (max N N')),
    adicEval_eq_sum J' hM' (x := ⇑φ ∘ x) (fun s => hφ _ (hx s)) f _ (le_degree_of_not_mem_Iic (max N N')), map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_mul, AlgHom.commutes, Finsupp.prod, Finsupp.prod, map_prod]
  simp only [map_pow, Function.comp_apply]

end Engine

section Torsion

variable {R : Type u} [CommRing R] {g : ℕ} (F : MvFormalGroup g R) [F.IsComm]
variable {C : Type v} [CommRing C] [Algebra R C]

omit [F.IsComm] in

theorem adicEval_nthSeries_sub_mem_sq (J : Ideal C) (hJ : IsNilpotent J) (I : Ideal C) (hIJ : I ≤ J) {x : Fin g → C}
    (hx : ∀ s, x s ∈ I) (n : ℕ) (i : Fin g) :
    MvFormalGroup.adicEval J x (F.nthSeries n i) - (n : C) * x i ∈ I ^ 2 := by
  classical
  haveI := isAdicComplete_of_isNilpotent J hJ
  have hxr : ∀ s, x s ∈ J.radical := fun s => Ideal.le_radical (hIJ (hx s))

  have hlin : MvFormalGroup.adicEval J x ((n : R) • (X i : MvPowerSeries (Fin g) R)) = (n : C) * x i := by
    rw [← coe_adicEvalAlgHom J hxr, map_smul, coe_adicEvalAlgHom J hxr, adicEval_X, Algebra.smul_def, map_natCast]
  have hsub : MvFormalGroup.adicEval J x (F.nthSeries n i) - (n : C) * x i =
      MvFormalGroup.adicEval J x (F.nthSeries n i - (n : R) • X i) := by
    rw [← hlin, ← coe_adicEvalAlgHom J hxr, ← map_sub]
  rw [hsub]
  apply adicEval_mem_pow J hJ I hIJ hx 2
  intro d hd
  rw [map_sub, map_smul]
  rcases Nat.lt_or_ge d.degree 1 with h0 | h1
  · have hd0 : d = 0 := (Finsupp.degree_eq_zero_iff d).mp (by omega)
    subst hd0
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_nthSeries F n i,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_X, smul_zero, sub_zero]
  · have hdeg : d.degree = 1 := by omega
    obtain ⟨s, rfl⟩ : ∃ s, Finsupp.single s 1 = d := by
      have hmem : d ∈ {d' : Fin g →₀ ℕ | d'.degree = 1} := hdeg
      rw [← Finsupp.range_single_one] at hmem
      exact hmem
    have hl := congrFun (congrFun (linearPart_nthSeries F n) i) s
    simp only [linearPart, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, nsmul_eq_mul] at hl
    rw [hl, coeff_X, smul_eq_mul]
    by_cases his : i = s
    · subst his; simp
    · rw [if_neg his, if_neg (fun h => his (Finsupp.single_left_injective one_ne_zero h).symm)]
      simp

variable {q K₀ : ℕ} (hqC : ((q : ℕ) : C) ^ K₀ = 0)
include hqC

omit [F.IsComm] in

theorem pow_nsmul_eq_zero (J : Ideal C) (hJ : IsNilpotent J) [IsAdicComplete J C] (I : Ideal C) (hIJ : I ≤ J)
    {e : ℕ} (hIe : I ^ e = ⊥) (y : Points F C J) (hy : ∀ i, y.val i ∈ I) : (q ^ K₀) ^ e • y = 0 := by

  have key : ∀ d : ℕ, ∀ i, ((q ^ K₀) ^ d • y).val i ∈ I ^ (d + 1) := by
    intro d
    induction d with
    | zero => intro i; rw [pow_zero, one_smul, zero_add, pow_one]; exact hy i
    | succ d ih =>
      intro i
      rw [show (q ^ K₀) ^ (d + 1) • y = (q ^ K₀) • ((q ^ K₀) ^ d • y) by rw [pow_succ', mul_smul],
        Points.val_nsmul]
      have hI' : I ^ (d + 1) ≤ J := (Ideal.pow_le_self (Nat.succ_ne_zero d)).trans hIJ
      have h := adicEval_nthSeries_sub_mem_sq F J hJ (I ^ (d + 1)) hI' ih (q ^ K₀) i
      have hzero : ((q ^ K₀ : ℕ) : C) * ((q ^ K₀) ^ d • y).val i = 0 := by
        rw [Nat.cast_pow, hqC, zero_mul]
      rw [hzero, sub_zero, ← pow_mul] at h
      exact Ideal.pow_le_pow_right (by omega) h
  ext i
  have h := key e i
  have hle : I ^ (e + 1) ≤ I ^ e := Ideal.pow_le_pow_right (Nat.le_succ e)
  have := hle h
  rw [hIe, Submodule.mem_bot] at this
  rw [this]
  rfl

omit [F.IsComm] in

theorem eq_zero_of_coprime_nsmul_eq_zero [Fact q.Prime] (J : Ideal C) (hJ : IsNilpotent J) [IsAdicComplete J C]
    {n : ℕ} (hn : n.Coprime q) (y : Points F C J) (hy : ∀ i, y.val i ∈ J) (h : n • y = 0) : y = 0 := by

  have hu : IsUnit (n : C) := by
    have hcop : (n ^ 1).Coprime (q ^ K₀) := Nat.Coprime.pow 1 K₀ hn
    rw [pow_one] at hcop
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have : (u : C) * n = 1 := by
      have h1 := congrArg (fun z : ℤ => (z : C)) huv
      simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_one, Int.cast_pow, Nat.cast_pow] at h1
      rw [hqC, mul_zero, add_zero] at h1
      exact h1
    exact IsUnit.of_mul_eq_one_right _ this
  obtain ⟨e, he⟩ := exists_pow_eq_bot hJ

  have key : ∀ d : ℕ, ∀ i, y.val i ∈ J ^ (d + 1) := by
    intro d
    induction d with
    | zero => intro i; rw [zero_add, pow_one]; exact hy i
    | succ d ih =>
      intro i
      have hI' : J ^ (d + 1) ≤ J := Ideal.pow_le_self (Nat.succ_ne_zero d)
      have h2 := adicEval_nthSeries_sub_mem_sq F J hJ (J ^ (d + 1)) hI' ih n i
      have hval : MvFormalGroup.adicEval J y.val (F.nthSeries n i) = 0 := by
        have := congrArg (fun z : Points F C J => z.val i) h
        simp only [Points.val_nsmul] at this
        exact this
      rw [hval, zero_sub, neg_mem_iff, ← pow_mul] at h2
      have h3 : y.val i ∈ J ^ ((d + 1) * 2) := by
        have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : C) h2
        rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this
      exact Ideal.pow_le_pow_right (by omega) h3
  ext i
  have h := key e i
  have hle : J ^ (e + 1) ≤ J ^ e := Ideal.pow_le_pow_right (Nat.le_succ e)
  have := hle h
  rw [he, Submodule.mem_bot] at this
  rw [this]
  rfl

theorem nsmul_cancel_of_coprime [Fact q.Prime] (J : Ideal C) (hJ : IsNilpotent J) [IsAdicComplete J C]
    {n : ℕ} (hn : n.Coprime q) (y y' : Points F C J) (hy : ∀ i, y.val i ∈ J) (hy' : ∀ i, y'.val i ∈ J)
    (h : n • y = n • y') : y = y' := by
  have hsub : ∀ i, (y - y').val i ∈ J := by
    intro i
    rw [sub_eq_add_neg, Points.val_add]
    refine adicEval_mem J hJ (fun s => ?_) (F.constantCoeff_eq_zero i)
    rcases s with s | s
    · exact hy s
    · simp only [Sum.elim_inr]
      rw [Points.val_neg]
      exact adicEval_mem J hJ hy' (constantCoeff_invSeries F s)
  have h0 : n • (y - y') = 0 := by rw [smul_sub, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_coprime_nsmul_eq_zero F hqC J hJ hn (y - y') hsub h0)

end Torsion

section EndExt

variable {B : Type u} [CommRing B] {g : ℕ} (F : MvFormalGroup g B) [F.IsComm]

theorem evalPoints_nsmul {C : Type v} [CommRing C] [Algebra B C] {J : Ideal C} [IsAdicComplete J C]
    (n : ℕ) (φ : MvFormalGroup.End F) (X : Points F C J) :
    Hom.evalPoints (n • φ) X = n • Hom.evalPoints φ X := by
  rw [nsmul_eq_mul, Hom.evalPoints_mul, Hom.evalPoints_natCast]

theorem evalPoints_add_end {C : Type v} [CommRing C] [Algebra B C] {J : Ideal C} [IsAdicComplete J C]
    (φ ψ : MvFormalGroup.End F) (X : Points F C J) :
    Hom.evalPoints (φ + ψ) X = Hom.evalPoints φ X + Hom.evalPoints ψ X :=
  Hom.evalPoints_add φ ψ X

omit [F.IsComm] in

theorem end_ext (φ ψ : MvFormalGroup.End F)
    (h : ∀ (C : Type u) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin g → C, (∀ s, x s ∈ J) → ∀ i, MvFormalGroup.adicEval J x (φ.toPowerSeries i) =
        MvFormalGroup.adicEval J x (ψ.toPowerSeries i)) : φ = ψ := by
  have hu := MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent F F
    (fun C _ _ J x => fun i => MvFormalGroup.adicEval J x (φ.toPowerSeries i))
    (fun C _ _ J hJ x hx i => adicEval_mem J hJ hx (φ.constantCoeff_eq_zero i))
    (fun C C' _ _ _ _ J J' hJ hJ' f hf x hx => by
      funext i
      exact (map_adicEval J hJ J' hJ' f hf hx (φ.toPowerSeries i)).symm)
    (fun C _ _ J hJ x y hx hy => by
      haveI := isAdicComplete_of_isNilpotent J hJ
      let X : Points F C J := ⟨x, fun s => Ideal.le_radical (hx s)⟩
      let Y : Points F C J := ⟨y, fun s => Ideal.le_radical (hy s)⟩
      have h1 := congrArg Points.val (map_add (Hom.evalPoints φ) X Y)
      exact h1)
  exact hu.unique (fun C _ _ J hJ x hx i => rfl) (fun C _ _ J hJ x hx i => h C J hJ x hx i)

omit [F.IsComm] in

theorem end_ext' (φ ψ : MvFormalGroup.End F)
    (h : ∀ (C : Type u) [CommRing C] [Algebra B C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
      ∀ X : Points F C J, (∀ i, X.val i ∈ J) → Hom.evalPoints φ X = Hom.evalPoints ψ X) : φ = ψ := by
  apply end_ext F φ ψ
  intro C _ _ J hJ x hx i
  haveI := isAdicComplete_of_isNilpotent J hJ
  have := h C J hJ ⟨x, fun s => Ideal.le_radical (hx s)⟩ hx
  exact congrFun (congrArg Points.val this) i

end EndExt

section Cong

variable {q : ℕ} [Fact q.Prime]

def Cong (M : ℕ) (c c' : Zp2 q × Zp2 q) : Prop :=
  c.1 - c'.1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ M} ∧ c.2 - c'.2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ M}

def tw (c c' : Zp2 q × Zp2 q) : Zp2 q × Zp2 q :=
  (c.1 * c'.1 + (q : Zp2 q) * (c.2 * WittVector.frobenius c'.2), c.1 * c'.2 + c.2 * WittVector.frobenius c'.1)

theorem cong_refl (M : ℕ) (c : Zp2 q × Zp2 q) : Cong M c c := by
  constructor <;> simp

theorem cong_symm {M : ℕ} {c c' : Zp2 q × Zp2 q} (h : Cong M c c') : Cong M c' c :=
  ⟨by rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 h.1, by rw [← neg_sub]; exact (Ideal.neg_mem_iff _).2 h.2⟩

theorem cong_trans {M : ℕ} {c c' c'' : Zp2 q × Zp2 q} (h : Cong M c c') (h' : Cong M c' c'') : Cong M c c'' :=
  ⟨by have := Ideal.add_mem _ h.1 h'.1; rwa [sub_add_sub_cancel] at this,
   by have := Ideal.add_mem _ h.2 h'.2; rwa [sub_add_sub_cancel] at this⟩

theorem cong_mono {M M' : ℕ} (hM : M ≤ M') {c c' : Zp2 q × Zp2 q} (h : Cong M' c c') : Cong M c c' :=
  ⟨Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hM) h.1,
   Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ hM) h.2⟩

theorem cong_add {M : ℕ} {c c' d d' : Zp2 q × Zp2 q} (h : Cong M c c') (h' : Cong M d d') :
    Cong M (c + d) (c' + d') :=
  ⟨by have := Ideal.add_mem _ h.1 h'.1; rwa [Prod.fst_add, Prod.fst_add, add_sub_add_comm],
   by have := Ideal.add_mem _ h.2 h'.2; rwa [Prod.snd_add, Prod.snd_add, add_sub_add_comm]⟩

theorem cong_sub {M : ℕ} {c c' d d' : Zp2 q × Zp2 q} (h : Cong M c c') (h' : Cong M d d') :
    Cong M (c - d) (c' - d') :=
  ⟨by have := Ideal.sub_mem _ h.1 h'.1; rwa [Prod.fst_sub, Prod.fst_sub, sub_sub_sub_comm],
   by have := Ideal.sub_mem _ h.2 h'.2; rwa [Prod.snd_sub, Prod.snd_sub, sub_sub_sub_comm]⟩

theorem cong_nsmul {M : ℕ} (n : ℕ) {c c' : Zp2 q × Zp2 q} (h : Cong M c c') : Cong M (n • c) (n • c') :=
  ⟨by have := Ideal.mul_mem_left _ (n : Zp2 q) h.1; rwa [Prod.smul_fst, Prod.smul_fst, nsmul_eq_mul, nsmul_eq_mul,
      ← mul_sub],
   by have := Ideal.mul_mem_left _ (n : Zp2 q) h.2; rwa [Prod.smul_snd, Prod.smul_snd, nsmul_eq_mul, nsmul_eq_mul,
      ← mul_sub]⟩

theorem frobenius_sub_mem {M : ℕ} {x y : Zp2 q} (h : x - y ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ M}) :
    WittVector.frobenius x - WittVector.frobenius y ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ M} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨z, hz⟩ := h
  refine ⟨WittVector.frobenius z, ?_⟩
  rw [← map_sub, hz, map_mul, map_pow, map_natCast]

theorem cong_tw {M : ℕ} {c c' d d' : Zp2 q × Zp2 q} (h : Cong M c c') (h' : Cong M d d') :
    Cong M (tw c d) (tw c' d') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h3, h4⟩ := h'
  have h4' := frobenius_sub_mem h4
  have h3' := frobenius_sub_mem h3
  set P := Ideal.span {((q : ℕ) : Zp2 q) ^ M}
  constructor
  · show c.1 * d.1 + (q : Zp2 q) * (c.2 * WittVector.frobenius d.2) -
        (c'.1 * d'.1 + (q : Zp2 q) * (c'.2 * WittVector.frobenius d'.2)) ∈ P
    have e : c.1 * d.1 + (q : Zp2 q) * (c.2 * WittVector.frobenius d.2) -
        (c'.1 * d'.1 + (q : Zp2 q) * (c'.2 * WittVector.frobenius d'.2)) =
        (c.1 - c'.1) * d.1 + c'.1 * (d.1 - d'.1) +
          (q : Zp2 q) * ((c.2 - c'.2) * WittVector.frobenius d.2 +
            c'.2 * (WittVector.frobenius d.2 - WittVector.frobenius d'.2)) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h3))
      (Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h2) (Ideal.mul_mem_left _ _ h4')))
  · show c.1 * d.2 + c.2 * WittVector.frobenius d.1 - (c'.1 * d'.2 + c'.2 * WittVector.frobenius d'.1) ∈ P
    have e : c.1 * d.2 + c.2 * WittVector.frobenius d.1 - (c'.1 * d'.2 + c'.2 * WittVector.frobenius d'.1) =
        (c.1 - c'.1) * d.2 + c'.1 * (d.2 - d'.2) +
          ((c.2 - c'.2) * WittVector.frobenius d.1 + c'.2 * (WittVector.frobenius d.1 - WittVector.frobenius d'.1)) := by
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_left _ _ h4))
      (Ideal.add_mem _ (Ideal.mul_mem_right _ _ h2) (Ideal.mul_mem_left _ _ h3'))

theorem tw_nsmul_left (n : ℕ) (c c' : Zp2 q × Zp2 q) : tw (n • c) c' = n • tw c c' := by
  obtain ⟨c₁, c₂⟩ := c
  obtain ⟨d₁, d₂⟩ := c'
  simp only [tw, Prod.smul_mk, nsmul_eq_mul, Prod.mk.injEq]
  constructor <;> ring

end Cong

section Construction

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]
variable {coord : ↥Λ → Zp2 q × Zp2 q} (hcoord : IsOrderCoord Λ q coord)
variable {B : Type u} [CommRing B] {K₀ : ℕ}
variable (F : MvFormalGroup 2 B) [F.IsComm] (ρ : ↥Λ →+ MvFormalGroup.End F)

def Sat (coord : ↥Λ → Zp2 q × Zp2 q) : Prop :=
  ∀ (K : ℕ) (m : ↥Λ), (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} →
    (coord m).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} → ∃ m' : ↥Λ, m = (q ^ K : ℕ) • m'

include hcoord in
theorem coord_sub (m m' : ↥Λ) : coord (m - m') = coord m - coord m' := by
  have h0 : coord 0 = 0 := by
    have h := hcoord.map_add 0 0
    rw [add_zero] at h
    exact add_eq_left.1 h.symm
  have hneg : coord (-m') = -coord m' := by
    have h := hcoord.map_add m' (-m')
    rw [add_neg_cancel, h0] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  rw [sub_eq_add_neg, hcoord.map_add, hneg, ← sub_eq_add_neg]

include hcoord in
theorem coord_nsmul (n : ℕ) (m : ↥Λ) : coord (n • m) = n • coord m := by
  have h0 : coord 0 = 0 := by
    have h := hcoord.map_add 0 0
    rw [add_zero] at h
    exact add_eq_left.1 h.symm
  induction n with
  | zero => rw [zero_smul, zero_smul, h0]
  | succ n ih => rw [succ_nsmul, hcoord.map_add, ih, succ_nsmul]

omit [Fact q.Prime] in
theorem natCast_pow_eq_zero (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (C : Type v) [CommRing C] [Algebra B C] :
    ((q : ℕ) : C) ^ K₀ = 0 := by
  rw [← map_natCast (algebraMap B C), ← map_pow, hK₀, map_zero]

theorem evalPoints_eq_zero_of_cong_zero (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord)
    (C : Type v) [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    [IsAdicComplete J C] (I : Ideal C) (hIJ : I ≤ J) {e : ℕ} (hIe : I ^ e = ⊥) (X : Points F C J)
    (hX : ∀ i, X.val i ∈ I) (m : ↥Λ) (hm : Cong (K₀ * e) (coord m) 0) : Hom.evalPoints (ρ m) X = 0 := by
  obtain ⟨m', rfl⟩ := hsat (K₀ * e) m (by simpa using hm.1) (by simpa using hm.2)
  rw [map_nsmul, evalPoints_nsmul, pow_mul]
  refine pow_nsmul_eq_zero F (natCast_pow_eq_zero hK₀ C) J hJ I hIJ hIe _ fun i => ?_
  rw [Hom.val_evalPoints]
  exact adicEval_mem' J hJ I hIJ hX ((ρ m').constantCoeff_eq_zero i)

include hcoord in

theorem evalPoints_eq_of_cong (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord)
    (C : Type v) [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    [IsAdicComplete J C] (I : Ideal C) (hIJ : I ≤ J) {e : ℕ} (hIe : I ^ e = ⊥) (X : Points F C J)
    (hX : ∀ i, X.val i ∈ I) (m m' : ↥Λ) (hm : Cong (K₀ * e) (coord m) (coord m')) :
    Hom.evalPoints (ρ m) X = Hom.evalPoints (ρ m') X := by
  have h : ρ m = ρ m' + ρ (m - m') := by rw [map_sub, add_sub_cancel]
  rw [h, evalPoints_add_end,
    evalPoints_eq_zero_of_cong_zero F ρ hK₀ hsat C J hJ I hIJ hIe X hX (m - m') ?_, add_zero]
  rw [coord_sub hcoord]
  have := cong_sub hm (cong_refl (K₀ * e) (coord m'))
  rwa [sub_self] at this

noncomputable def apx (M : ℕ) (c : Zp2 q × Zp2 q) : ↥Λ := Classical.choose (hcoord.dense M c.1 c.2)

theorem cong_apx (M : ℕ) (c : Zp2 q × Zp2 q) : Cong M (coord (apx hcoord M c)) c :=
  Classical.choose_spec (hcoord.dense M c.1 c.2)

noncomputable def expo {C : Type v} [CommRing C] (J : Ideal C) : ℕ :=
  by classical exact if h : IsNilpotent J then Classical.choose h else 0

theorem pow_expo {C : Type v} [CommRing C] {J : Ideal C} (hJ : IsNilpotent J) : J ^ expo J = ⊥ := by
  classical
  unfold expo
  rw [dif_pos hJ]
  exact Classical.choose_spec hJ

variable (K₀) in

noncomputable def fam (c : Zp2 q × Zp2 q) (C : Type u) [CommRing C] [Algebra B C] (J : Ideal C) (x : Fin 2 → C) :
    Fin 2 → C :=
  fun i => MvFormalGroup.adicEval J x ((ρ (apx hcoord (K₀ * expo J) c)).toPowerSeries i)

theorem fam_nat (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (c : Zp2 q × Zp2 q)
    (C C' : Type u) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
    (J : Ideal C) (J' : Ideal C') (hJ : IsNilpotent J) (hJ' : IsNilpotent J') (φ : C →ₐ[B] C')
    (hφ : ∀ s ∈ J, φ s ∈ J') (x : Fin 2 → C) (hx : ∀ j, x j ∈ J) :
    fam hcoord K₀ F ρ c C' J' (φ ∘ x) = φ ∘ fam hcoord K₀ F ρ c C J x := by
  haveI := isAdicComplete_of_isNilpotent J' hJ'

  set I₀ : Ideal C := Ideal.span (Set.range x) with hI₀
  have hI₀J : I₀ ≤ J := Ideal.span_le.2 (by rintro _ ⟨s, rfl⟩; exact hx s)
  set I' : Ideal C' := I₀.map φ with hI'
  have hI'J' : I' ≤ J' := by
    rw [hI', Ideal.map_le_iff_le_comap]
    intro s hs
    exact hφ s (hI₀J hs)
  have hxI' : ∀ s, (φ ∘ x) s ∈ I' := fun s => Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨s, rfl⟩)
  have hpow1 : I' ^ expo J = ⊥ := by
    rw [hI', ← Ideal.map_pow, ← le_bot_iff]
    have : I₀ ^ expo J = ⊥ := le_bot_iff.1 ((Ideal.pow_right_mono hI₀J _).trans (pow_expo hJ).le)
    rw [this, Ideal.map_bot]
  have hpow2 : I' ^ expo J' = ⊥ := le_bot_iff.1 ((Ideal.pow_right_mono hI'J' _).trans (pow_expo hJ').le)
  have hpow : I' ^ min (expo J) (expo J') = ⊥ := by
    rcases le_total (expo J) (expo J') with h | h
    · rw [min_eq_left h]; exact hpow1
    · rw [min_eq_right h]; exact hpow2
  let X' : Points F C' J' := ⟨φ ∘ x, fun s => Ideal.le_radical (hI'J' (hxI' s))⟩
  have key := evalPoints_eq_of_cong hcoord F ρ hK₀ hsat C' J' hJ' I' hI'J' hpow X' hxI'
    (apx hcoord (K₀ * expo J') c) (apx hcoord (K₀ * expo J) c)
    (cong_trans (cong_mono (Nat.mul_le_mul_left K₀ (min_le_right _ _)) (cong_apx hcoord _ c))
      (cong_symm (cong_mono (Nat.mul_le_mul_left K₀ (min_le_left _ _)) (cong_apx hcoord _ c))))
  funext i
  have h1 := congrFun (congrArg Points.val key) i
  simp only [Hom.val_evalPoints, X'] at h1
  show MvFormalGroup.adicEval J' (φ ∘ x) _ = φ (MvFormalGroup.adicEval J x _)
  rw [h1, map_adicEval J hJ J' hJ' φ hφ hx]

theorem existsUnique_psi (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (c : Zp2 q × Zp2 q) :
    ∃! ψ : MvFormalGroup.End F,
    ∀ (C : Type u) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin 2 → C, (∀ j, x j ∈ J) → ∀ i, fam hcoord K₀ F ρ c C J x i =
        MvFormalGroup.adicEval J x (ψ.toPowerSeries i) :=
  MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent F F (fam hcoord K₀ F ρ c)
    (fun C _ _ J hJ x hx i => adicEval_mem J hJ hx ((ρ _).constantCoeff_eq_zero i))
    (fun C C' _ _ _ _ J J' hJ hJ' φ hφ x hx => fam_nat hcoord F ρ hK₀ hsat c C C' J J' hJ hJ' φ hφ x hx)
    (fun C _ _ J hJ x y hx hy => by
      haveI := isAdicComplete_of_isNilpotent J hJ
      let X : Points F C J := ⟨x, fun s => Ideal.le_radical (hx s)⟩
      let Y : Points F C J := ⟨y, fun s => Ideal.le_radical (hy s)⟩
      exact congrArg Points.val (map_add (Hom.evalPoints (ρ (apx hcoord (K₀ * expo J) c))) X Y))

noncomputable def psi (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (c : Zp2 q × Zp2 q) : MvFormalGroup.End F :=
  Classical.choose (existsUnique_psi hcoord F ρ hK₀ hsat c).exists

theorem psi_spec (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (c : Zp2 q × Zp2 q)
    (C : Type u) [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    (x : Fin 2 → C) (hx : ∀ j, x j ∈ J) (i : Fin 2) :
    fam hcoord K₀ F ρ c C J x i = MvFormalGroup.adicEval J x ((psi hcoord F ρ hK₀ hsat c).toPowerSeries i) :=
  Classical.choose_spec (existsUnique_psi hcoord F ρ hK₀ hsat c).exists C J hJ x hx i

theorem evalPoints_psi (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (c : Zp2 q × Zp2 q)
    (C : Type u) [CommRing C] [Algebra B C] (J : Ideal C) (hJ : IsNilpotent J)
    [IsAdicComplete J C] {e : ℕ} (hJe : J ^ e = ⊥) (X : Points F C J) (hX : ∀ i, X.val i ∈ J)
    (m : ↥Λ) (hm : Cong (K₀ * e) (coord m) c) :
    Hom.evalPoints (psi hcoord F ρ hK₀ hsat c) X = Hom.evalPoints (ρ m) X := by
  have hmin : J ^ min e (expo J) = ⊥ := by
    rcases le_total e (expo J) with h | h
    · rw [min_eq_left h]; exact hJe
    · rw [min_eq_right h]; exact pow_expo hJ
  have key := evalPoints_eq_of_cong hcoord F ρ hK₀ hsat C J hJ J le_rfl hmin X hX (apx hcoord (K₀ * expo J) c) m
    (cong_trans (cong_mono (Nat.mul_le_mul_left K₀ (min_le_right _ _)) (cong_apx hcoord _ c))
      (cong_symm (cong_mono (Nat.mul_le_mul_left K₀ (min_le_left _ _)) hm)))
  rw [← key]
  ext i
  rw [Hom.val_evalPoints, Hom.val_evalPoints, ← psi_spec hcoord F ρ hK₀ hsat c C J hJ X.val hX i]
  rfl

theorem psi_add (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (c c' : Zp2 q × Zp2 q) :
    psi hcoord F ρ hK₀ hsat (c + c') = psi hcoord F ρ hK₀ hsat c + psi hcoord F ρ hK₀ hsat c' := by
  apply end_ext' F
  intro C _ _ J _ hJ X hX
  obtain ⟨e, he⟩ := exists_pow_eq_bot hJ
  rw [evalPoints_add_end,
    evalPoints_psi hcoord F ρ hK₀ hsat c C J hJ he X hX _ (cong_apx hcoord (K₀ * e) c),
    evalPoints_psi hcoord F ρ hK₀ hsat c' C J hJ he X hX _ (cong_apx hcoord (K₀ * e) c'),
    evalPoints_psi hcoord F ρ hK₀ hsat (c + c') C J hJ he X hX (apx hcoord (K₀ * e) c + apx hcoord (K₀ * e) c')
      (by rw [hcoord.map_add]; exact cong_add (cong_apx hcoord _ c) (cong_apx hcoord _ c')),
    map_add, evalPoints_add_end]

noncomputable def psiA (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) : (Zp2 q × Zp2 q) →+ MvFormalGroup.End F where
  toFun := psi hcoord F ρ hK₀ hsat
  map_zero' := by
    have h := psi_add hcoord F ρ hK₀ hsat 0 0
    rw [add_zero] at h
    exact add_eq_left.1 h.symm
  map_add' := psi_add hcoord F ρ hK₀ hsat

def MulCompat (ρ : ↥Λ →+ MvFormalGroup.End F) : Prop :=
  ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
    ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m * ρ m'

variable (Λ q) in

def Prods : Prop :=
  ∀ m m' : ↥Λ, ∃ n : ℕ, n.Coprime q ∧ (n : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) ∈ Λ

theorem psi_tw (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (hmul : MulCompat F ρ) (hprod : Prods Λ q)
    (c c' : Zp2 q × Zp2 q) :
    psi hcoord F ρ hK₀ hsat (tw c c') = psi hcoord F ρ hK₀ hsat c * psi hcoord F ρ hK₀ hsat c' := by
  apply end_ext' F
  intro C _ _ J _ hJ X hX
  obtain ⟨e, he⟩ := exists_pow_eq_bot hJ
  set m := apx hcoord (K₀ * e) c with hm
  set m' := apx hcoord (K₀ * e) c' with hm'
  obtain ⟨n, hn, hp⟩ := hprod m m'

  have hcoe : ((n • m : ↥Λ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) = (n : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) := by
    rw [Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul, smul_mul_assoc]
  have hp' : ((n • m : ↥Λ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ := by rw [hcoe]; exact hp
  have hρp : ρ ⟨_, hp'⟩ = ρ (n • m) * ρ m' := hmul (n • m) m' hp'
  have hcp : Cong (K₀ * e) (coord ⟨_, hp'⟩) (n • tw c c') := by
    rw [hcoord.map_mul (n • m) m' hp', coord_nsmul hcoord]
    change Cong (K₀ * e) (tw (n • coord m) (coord m')) (n • tw c c')
    rw [tw_nsmul_left]
    exact cong_nsmul n (cong_tw (cong_apx hcoord _ c) (cong_apx hcoord _ c'))

  have hY : ∀ i, (Hom.evalPoints (ρ m') X).val i ∈ J := fun i => by
    rw [Hom.val_evalPoints]; exact adicEval_mem J hJ hX ((ρ m').constantCoeff_eq_zero i)
  have h1 : Hom.evalPoints (psi hcoord F ρ hK₀ hsat (n • tw c c')) X =
      n • Hom.evalPoints (psi hcoord F ρ hK₀ hsat c * psi hcoord F ρ hK₀ hsat c') X := by
    rw [evalPoints_psi hcoord F ρ hK₀ hsat _ C J hJ he X hX _ hcp, hρp, Hom.evalPoints_mul, map_nsmul,
      evalPoints_nsmul, Hom.evalPoints_mul,
      evalPoints_psi hcoord F ρ hK₀ hsat c' C J hJ he X hX m' (cong_apx hcoord _ c'),
      evalPoints_psi hcoord F ρ hK₀ hsat c C J hJ he _ hY m (cong_apx hcoord _ c)]
  have h2 : psi hcoord F ρ hK₀ hsat (n • tw c c') = n • psi hcoord F ρ hK₀ hsat (tw c c') :=
    map_nsmul (psiA hcoord F ρ hK₀ hsat) n (tw c c')
  rw [h2, evalPoints_nsmul] at h1
  refine nsmul_cancel_of_coprime F (natCast_pow_eq_zero hK₀ C) J hJ hn _ _ (fun i => ?_) (fun i => ?_) h1
  · rw [Hom.val_evalPoints]; exact adicEval_mem J hJ hX (Hom.constantCoeff_eq_zero _ i)
  · rw [Hom.val_evalPoints]; exact adicEval_mem J hJ hX (Hom.constantCoeff_eq_zero _ i)

def UnitCompat (coord : ↥Λ → Zp2 q × Zp2 q) (ρ : ↥Λ →+ MvFormalGroup.End F) : Prop :=
  ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
    coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧ (ρ ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩).toPowerSeries = F.nthSeries n

theorem psi_one (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (hunit : UnitCompat F coord ρ) :
    psi hcoord F ρ hK₀ hsat (1, 0) = 1 := by
  obtain ⟨n, hn, h1, hc1, hρ1⟩ := hunit
  have hρn : ρ ⟨((n : ℚ) : ℍ[ℚ, a, b]), h1⟩ = (n : MvFormalGroup.End F) := by
    apply MvFormalGroup.Hom.ext
    rw [hρ1, End.toPowerSeries_natCast]
  apply end_ext' F
  intro C _ _ J _ hJ X hX
  obtain ⟨e, he⟩ := exists_pow_eq_bot hJ
  have key : Hom.evalPoints (psi hcoord F ρ hK₀ hsat ((n : Zp2 q), 0)) X = n • X := by
    rw [evalPoints_psi hcoord F ρ hK₀ hsat _ C J hJ he X hX _ (by rw [hc1]; exact cong_refl _ _), hρn,
      Hom.evalPoints_natCast]
  have hn1 : ((n : Zp2 q), (0 : Zp2 q)) = n • ((1 : Zp2 q), (0 : Zp2 q)) := by
    rw [Prod.smul_mk, nsmul_eq_mul, mul_one, smul_zero]
  rw [hn1, show psi hcoord F ρ hK₀ hsat (n • ((1 : Zp2 q), (0 : Zp2 q))) = n • psi hcoord F ρ hK₀ hsat (1, 0) from
    map_nsmul (psiA hcoord F ρ hK₀ hsat) n _, evalPoints_nsmul] at key
  rw [Hom.evalPoints_one]
  refine nsmul_cancel_of_coprime F (natCast_pow_eq_zero hK₀ C) J hJ hn _ _ (fun i => ?_) hX key
  rw [Hom.val_evalPoints]; exact adicEval_mem J hJ hX (Hom.constantCoeff_eq_zero _ i)

theorem psi_coord (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (m : ↥Λ) :
    psi hcoord F ρ hK₀ hsat (coord m) = ρ m := by
  apply end_ext' F
  intro C _ _ J _ hJ X hX
  obtain ⟨e, he⟩ := exists_pow_eq_bot hJ
  exact evalPoints_psi hcoord F ρ hK₀ hsat _ C J hJ he X hX m (cong_refl _ _)

theorem exists_actRingHom (hK₀ : ((q : ℕ) : B) ^ K₀ = 0) (hsat : Sat coord) (hmul : MulCompat F ρ)
    (hprod : Prods Λ q) (hunit : UnitCompat F coord ρ) :
    ∃ A : Zp2 q →+* MvFormalGroup.End F, ∀ x, A x = psi hcoord F ρ hK₀ hsat (x, 0) := by
  refine ⟨
    { toFun := fun x => psi hcoord F ρ hK₀ hsat (x, 0)
      map_one' := psi_one hcoord F ρ hK₀ hsat hunit
      map_mul' := fun x y => ?_
      map_zero' := ?_
      map_add' := fun x y => ?_ }, fun x => rfl⟩
  · have h := psi_tw hcoord F ρ hK₀ hsat hmul hprod (x, 0) (y, 0)
    simp only [tw, mul_zero, map_zero, zero_mul, add_zero] at h
    exact h
  · exact (psiA hcoord F ρ hK₀ hsat).map_zero
  · have h := psi_add hcoord F ρ hK₀ hsat (x, 0) (y, 0)
    rw [Prod.mk_add_mk, add_zero] at h
    exact h

end Construction

end D2aExtension

open D2aExtension in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : CerednikDrinfeld.QM.IsOrderCoord Λ q coord)
    (B : Type u) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B))
    (F : MvFormalGroup 2 B) [F.IsComm] (ρ : ↥Λ → MvFormalGroup.End F)
    (hadd : ∀ m m' : ↥Λ, ρ (m + m') = ρ m + ρ m')
    (hmul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
      ρ ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = ρ m * ρ m')
    (hunit : ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧
        (ρ ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩).toPowerSeries = F.nthSeries n) :
    ∃ X : FormalODModule q B, X.F = F ∧
      ∀ m : ↥Λ, Series.addVia F (X.act (coord m).1) ((X.act (coord m).2).comp X.varpi) =
        (ρ m).toPowerSeries := by
  classical
  obtain ⟨K₀, hK₀⟩ := hq
  obtain ⟨hsat, -, hprod, -⟩ :=
    CerednikDrinfeld.QM.IsOrderCoord.exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime coord hcoord

  let ρA : ↥Λ →+ MvFormalGroup.End F :=
    { toFun := ρ
      map_zero' := by
        have h := hadd 0 0
        rw [add_zero] at h
        exact add_eq_left.1 h.symm
      map_add' := hadd }
  have hρA : ∀ m, ρA m = ρ m := fun m => rfl
  obtain ⟨A, hA⟩ := exists_actRingHom hcoord F ρA hK₀ hsat (fun m m' h => hmul m m' h) hprod
    (by obtain ⟨n, hn, h, hc, hρ⟩ := hunit; exact ⟨n, hn, h, hc, hρ⟩)
  have htw := psi_tw hcoord F ρA hK₀ hsat (fun m m' h => hmul m m' h) hprod
  set ϖ : MvFormalGroup.End F := psi hcoord F ρA hK₀ hsat (0, 1) with hϖ

  have hvv : ϖ * ϖ = A (q : Zp2 q) := by
    rw [hA, hϖ, ← htw]
    congr 1
    simp [tw]
  have hva : ∀ x, ϖ * A x = A (WittVector.frobenius x) * ϖ := by
    intro x
    rw [hA, hA, hϖ, ← htw, ← htw]
    congr 1
    simp only [tw, mul_zero, zero_mul, zero_add, map_zero, one_mul, add_zero, mul_one]
  refine ⟨
    { F := F
      isComm := inferInstance
      act := fun x => (A x).toPowerSeries
      varpi := ϖ.toPowerSeries
      isLawHom_act := fun x => IsLawHom.of_hom _
      isLawHom_varpi := IsLawHom.of_hom _
      act_one := ?_
      act_mul := ?_
      act_add := ?_
      varpi_comp_varpi := ?_
      varpi_comp_act := ?_ }, rfl, ?_⟩
  · rw [map_one]; rfl
  · intro x y; rw [map_mul]; rfl
  · intro x y; rw [map_add]; rfl
  · show (ϖ * ϖ).toPowerSeries = _
    rw [hvv]
  · intro x
    show (ϖ * A x).toPowerSeries = (A (WittVector.frobenius x) * ϖ).toPowerSeries
    rw [hva]
  · intro m
    show (A (coord m).1 + A (coord m).2 * ϖ).toPowerSeries = (ρ m).toPowerSeries
    congr 1
    rw [hA, hA, hϖ, ← htw, ← psi_add hcoord F ρA hK₀ hsat, ← hρA m, ← psi_coord hcoord F ρA hK₀ hsat m]
    congr 1
    simp [tw]

end

end S_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_F_eq_and_addVia_act_eq_of_isOrderCoord_of_isNilpotent (solution)
