-- Prove2me | solution 1 for Deformation.map_scaledLogTrunc_mem_span_pow_of_mvFormalGroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/c4b454d8-8ece-5c26-9c72-36616025736e

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_map_scaledLogTrunc_mem_span_pow_of_mvFormalGroup

set_option autoImplicit false

namespace S17L2d

open MvPowerSeries

section Rescale

variable {𝓞 : Type*} [CommRing 𝓞] {σ : Type*}

noncomputable def rho (p : ℕ) : MvPowerSeries σ 𝓞 →+* MvPowerSeries σ 𝓞 := rescale (fun _ => (p : 𝓞))

theorem coeff_rho (p : ℕ) (f : MvPowerSeries σ 𝓞) (m : σ →₀ ℕ) :
    coeff m (rho p f) = (p : 𝓞) ^ m.degree * coeff m f := by
  rw [rho, coeff_rescale]
  congr 1
  rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.degree]
  rfl

theorem rho_natCast (p n : ℕ) : rho (σ := σ) (𝓞 := 𝓞) p (n : MvPowerSeries σ 𝓞) = n := map_natCast _ n

theorem rho_eq_subst (p : ℕ) (f : MvPowerSeries σ 𝓞) :
    rho p f = subst ((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) f :=
  rescale_eq_subst _ f

theorem rho_X (p : ℕ) (s : σ) : rho (𝓞 := 𝓞) p (X s) = (p : 𝓞) • X s := by
  rw [rho_eq_subst, subst_X (HasSubst.smul_X _)]
  rfl

theorem rho_subst (p : ℕ) {τ : Type*} {a : τ → MvPowerSeries σ 𝓞} (ha : HasSubst a) (f : MvPowerSeries τ 𝓞) :
    rho p (subst a f) = subst (fun t => rho p (a t)) f := by
  rw [rho_eq_subst, subst_comp_subst_apply ha (HasSubst.smul_X _)]
  congr 1
  funext t
  rw [rho_eq_subst]

theorem subst_smul_family (p : ℕ) {τ : Type*} {a : σ → MvPowerSeries τ 𝓞} (ha : HasSubst a) (f : MvPowerSeries σ 𝓞) :
    subst (fun s => (p : 𝓞) • a s) f = subst a (rho p f) := by
  rw [rho_eq_subst, subst_comp_subst_apply (HasSubst.smul_X _) ha]
  congr 1
  funext s
  show (p : 𝓞) • a s = subst a (((fun _ : σ => (p : 𝓞)) • (X : σ → MvPowerSeries σ 𝓞)) s)
  rw [Pi.smul_apply', subst_smul ha, subst_X ha]

theorem coeff_eq_zero_of_coeff_rho {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {f : MvPowerSeries σ 𝓞}
    {m : σ →₀ ℕ} (h : coeff m (rho p f) = 0) : coeff m f = 0 := by
  rw [coeff_rho] at h
  exact (mem_nonZeroDivisors_iff.1 (pow_mem hp m.degree)).1 _ h

theorem subst_zero_family {τ : Type*} (f : MvPowerSeries σ 𝓞) :
    subst (fun _ : σ => (0 : MvPowerSeries τ 𝓞)) f = C (constantCoeff f) := by
  classical
  ext e
  rw [coeff_subst HasSubst.zero, finsum_eq_single _ (0 : σ →₀ ℕ)]
  · rw [Finsupp.prod_zero_index, coeff_zero_eq_constantCoeff, smul_eq_mul, coeff_one, coeff_C]
    split_ifs <;> simp
  · intro d hd
    obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 hd
    rw [Finsupp.prod, Finset.prod_eq_zero hs (by rw [zero_pow (Finsupp.mem_support_iff.1 hs)]),
      map_zero, smul_zero]

end Rescale

section Law

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} {d : ℕ}

noncomputable def Hp (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) : ℕ → Fin d → MvPowerSeries (Fin d) 𝓞
  | 0 => fun _ => 0
  | n + 1 => fun i => subst (Sum.elim (Hp Fp n) fun j => X j) (Fp i)

variable (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞) (hFp0 : ∀ i, (Fp i).constantCoeff = 0)

theorem Hp_zero : Hp Fp 0 = fun _ => 0 := rfl

theorem Hp_succ (n : ℕ) : Hp Fp (n + 1) = fun i => subst (Sum.elim (Hp Fp n) fun j => X j) (Fp i) := rfl

include hFp0 in
theorem constantCoeff_Hp (n : ℕ) : ∀ i, (Hp Fp n i).constantCoeff = 0 := by
  induction n with
  | zero => intro i; rw [Hp_zero, map_zero]
  | succ n ih =>
    intro i
    rw [Hp_succ]
    exact constantCoeff_subst_eq_zero
      (MvFormalGroup.hasSubst_elim ih (fun j => constantCoeff_X j))
      (fun s => by rcases s with j | j <;> simp [ih j, constantCoeff_X]) (hFp0 i)

include hFp0 in
theorem hasSubst_Hp_elim (n : ℕ) : HasSubst (Sum.elim (Hp Fp n) fun j => (X j : MvPowerSeries (Fin d) 𝓞)) :=
  MvFormalGroup.hasSubst_elim (constantCoeff_Hp Fp hFp0 n) (fun j => constantCoeff_X j)

include hFp0 in
theorem hasSubst_Hp (n : ℕ) : HasSubst (Hp Fp n) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_Hp Fp hFp0 n)

include hFp0 in

theorem subst_Hp_eq_nsmul (φ : Fin d → MvPowerSeries (Fin d) 𝓞) (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (n : ℕ) (i : Fin d) : subst (Hp Fp n) (φ i) = n • φ i := by
  induction n with
  | zero =>
    rw [Hp_zero, zero_smul, subst_zero_family, hφ0, map_zero]
  | succ n ih =>
    have hE := hasSubst_Hp_elim Fp hFp0 n
    have hinl : HasSubst (fun j : Fin d => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
    have hinr : HasSubst (fun j : Fin d => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) :=
      hasSubst_of_constantCoeff_zero (fun j => constantCoeff_X _)
    rw [Hp_succ, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero hFp0) hE, hφF, subst_add hE,
      subst_comp_subst_apply hinl hE, subst_comp_subst_apply hinr hE]
    simp only [subst_X hE, Sum.elim_inl, Sum.elim_inr]
    rw [show (fun j => Hp Fp n j) = Hp Fp n from rfl, ih,
      show (fun j => (X j : MvPowerSeries (Fin d) 𝓞)) = X from rfl,
      show subst (X : Fin d → MvPowerSeries (Fin d) 𝓞) (φ i) = φ i from congrFun subst_self (φ i),
      succ_nsmul]

variable (F : MvFormalGroup d 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)

include hFp hFp0 in

theorem rho_law (i : Fin d) : rho p (F.toPowerSeries i) = (p : 𝓞) • Fp i := by
  ext m
  rw [coeff_rho, map_smul, smul_eq_mul]
  by_cases hm : m = 0
  · subst hm
    simp only [coeff_zero_eq_constantCoeff, F.constantCoeff_eq_zero, hFp0, mul_zero]
  · rw [← hFp i m hm, mul_comm]

include hFp hFp0 in

theorem rho_nthSeries (n : ℕ) (i : Fin d) : rho p (F.nthSeries n i) = (p : 𝓞) • Hp Fp n i := by
  induction n generalizing i with
  | zero => simp [MvFormalGroup.nthSeries_zero, Hp_zero]
  | succ n ih =>
    rw [MvFormalGroup.nthSeries_succ, Hp_succ]
    dsimp only
    have hH : HasSubst (Sum.elim (F.nthSeries n) fun j => (X j : MvPowerSeries (Fin d) 𝓞)) :=
      MvFormalGroup.hasSubst_elim (MvFormalGroup.constantCoeff_nthSeries F n) (fun j => constantCoeff_X j)
    rw [rho_subst p hH]
    have hfam : (fun t => rho p (Sum.elim (F.nthSeries n) (fun j => (X j : MvPowerSeries (Fin d) 𝓞)) t)) =
        fun t => (p : 𝓞) • Sum.elim (Hp Fp n) (fun j => (X j : MvPowerSeries (Fin d) 𝓞)) t := by
      funext t
      rcases t with j | j
      · simp only [Sum.elim_inl, ih j]
      · simp only [Sum.elim_inr, rho_X]
    rw [hfam, subst_smul_family p (hasSubst_Hp_elim Fp hFp0 n), rho_law Fp hFp0 F hFp,
      subst_smul (hasSubst_Hp_elim Fp hFp0 n)]

end Law

section Arith

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime] {d : ℕ}

omit hp in
theorem mem_span_pow_of_pow_mul_mem (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) {a : 𝓞} {K e : ℕ} (hKe : K ≤ e)
    (h : (p : 𝓞) ^ K * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ (e - K)} := by
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  have h0 : (p : 𝓞) ^ K * (b * (p : 𝓞) ^ (e - K) - a) = 0 := by
    rw [mul_sub, sub_eq_zero, ← hb, mul_comm ((p : 𝓞) ^ K), mul_assoc, ← pow_add, Nat.sub_add_cancel hKe]
  exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 (pow_mem hpR K)).1 _ h0)

theorem mem_span_pow_of_natCast_mul_mem {u : ℕ} (hu : ¬ p ∣ u) {a : 𝓞} {e : ℕ}
    (h : (u : 𝓞) * a ∈ Ideal.span {(p : 𝓞) ^ e}) : a ∈ Ideal.span {(p : 𝓞) ^ e} := by
  have hcop : IsCoprime (u : ℤ) ((p : ℤ) ^ e) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right e ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu).symm)
  obtain ⟨x, y, hxy⟩ := hcop
  have h1 : ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) = 1 := by
    have := congrArg (Int.castRingHom 𝓞) hxy
    simpa using this
  have : a = (x : 𝓞) * ((u : 𝓞) * a) + (p : 𝓞) ^ e * ((y : 𝓞) * a) := by
    calc a = ((x : 𝓞) * (u : 𝓞) + (y : 𝓞) * (p : 𝓞) ^ e) * a := by rw [h1, one_mul]
      _ = _ := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

omit hp in
theorem natCast_mul_coeff_mem (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (M' : Fin d →₀ ℕ) (i : Fin d) (hi : 1 ≤ M' i) :
    ((M' i : ℕ) : 𝓞) * coeff M' φi ∈ Ideal.span {(p : 𝓞) ^ (M'.degree - 1)} := by
  have hle : Finsupp.single i 1 ≤ M' := Finsupp.single_le_iff.2 hi
  set m := M' - Finsupp.single i 1 with hm
  have hM : m + Finsupp.single i 1 = M' := tsub_add_cancel_of_le hle
  have h1 : m i + 1 = M' i := by
    conv_rhs => rw [← hM]
    simp
  have h2 : m.degree = M'.degree - 1 := by
    conv_rhs => rw [← hM]
    rw [map_add, Finsupp.degree_single]
    simp
  have := hint i m
  rwa [h1, hM, h2] at this

theorem pow_degree_mul_coeff_eq (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (φi : MvPowerSeries (Fin d) 𝓞)
    (hint : ∀ (j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) φi ∈ Ideal.span {(p : 𝓞) ^ m.degree})
    (N : ℕ) (G : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * φi.coeff m) ∧
      (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = φi.coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ φi.coeff m)))
    (m : Fin d →₀ ℕ) (hm : m.degree < p ^ N) :
    (p : 𝓞) ^ m.degree * coeff m G = (p : 𝓞) ^ N * coeff m φi := by
  rcases le_or_gt m.degree N with hle | hlt
  · rw [show coeff m G = G.coeff m from rfl, (hG m).1 hle, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  ·
    have hdiv : (p : 𝓞) ^ (m.degree - N) ∣ coeff m φi := by
      have hm0 : m ≠ 0 := by rintro rfl; simp at hlt
      obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
        by_contra h
        exact hm0 (Finsupp.ext fun j => not_not.1 (not_exists.1 h j))
      obtain ⟨k, u, hu, hk⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj p hp.out.ne_one
      have hu0 : u ≠ 0 := fun h => hj (by rw [hk, h, mul_zero])
      have hkj : p ^ k ≤ m j := by rw [hk]; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
      have hjdeg : m j ≤ m.degree := Finsupp.le_degree j m
      have hkN : k < N := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 (lt_of_le_of_lt (hkj.trans hjdeg) hm)
      have hkdeg : k < m.degree := lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) (hkj.trans hjdeg)
      have hA := natCast_mul_coeff_mem φi hint m j (Nat.one_le_iff_ne_zero.2 hj)
      rw [hk, Nat.cast_mul, Nat.cast_pow, mul_comm ((p : 𝓞) ^ k) (u : 𝓞), mul_assoc] at hA
      have hB := mem_span_pow_of_pow_mul_mem hpR (by omega) (mem_span_pow_of_natCast_mul_mem hu hA)
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hB
      refine ⟨(p : 𝓞) ^ (m.degree - 1 - k - (m.degree - N)) * b, ?_⟩
      rw [← hb, mul_comm b, ← mul_assoc, ← pow_add, show m.degree - N + (m.degree - 1 - k - (m.degree - N)) =
        m.degree - 1 - k by omega]
    rcases (hG m).2 hlt with h | ⟨-, h⟩
    · obtain ⟨t, ht⟩ : ∃ t, m.degree = N + t := ⟨m.degree - N, by omega⟩
      rw [show coeff m φi = φi.coeff m from rfl, ← h, show G.coeff m = coeff m G from rfl, ht,
        Nat.add_sub_cancel_left, pow_add]
      ring
    · exact absurd hdiv h

end Arith

section Shadow

variable {𝓞 : Type*} [CommRing 𝓞] {p : ℕ} [hp : Fact p.Prime] {d : ℕ}
  (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞) (F : MvFormalGroup d 𝓞)
  (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
  (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
  (φ : Fin d → MvPowerSeries (Fin d) 𝓞) (hφ0 : ∀ i, (φ i).constantCoeff = 0)
  (hφF : ∀ i, subst Fp (φ i) =
    subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
      subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
  (hint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
    ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) (φ i) ∈ Ideal.span {(p : 𝓞) ^ m.degree})

include hpR hFp hFp0 hφ0 hφF hint in
theorem coeff_shadow_eq_zero (v N : ℕ) (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞)
    (hG : ∀ m : Fin d →₀ ℕ,
      (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
      (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
        (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m)))
    (m : Fin d →₀ ℕ) (hm : m.degree < p ^ N) :
    coeff m (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) = 0 := by
  apply coeff_eq_zero_of_coeff_rho (p := p) hpR

  set T : MvPowerSeries (Fin d) 𝓞 := (p : 𝓞) ^ N • φ i - rho p G with hT
  have hTcoeff : ∀ m' : Fin d →₀ ℕ, m'.degree < p ^ N → coeff m' T = 0 := by
    intro m' hm'
    rw [hT, map_sub, map_smul, smul_eq_mul, coeff_rho, pow_degree_mul_coeff_eq hpR (φ i) (hint i) N G hG m' hm',
      sub_self]
  have hTord : ((p ^ N : ℕ) : ℕ∞) ≤ T.order :=
    nat_le_order fun m' hm' => hTcoeff m' (by exact_mod_cast hm')
  have hH : HasSubst (F.nthSeries (p ^ v)) :=
    hasSubst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries F _)
  have hHp := hasSubst_Hp Fp hFp0 (p ^ v)

  have h1 : rho p (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) =
      subst (Hp Fp (p ^ v)) (rho p G) - (p : MvPowerSeries (Fin d) 𝓞) ^ v * rho p G := by
    rw [map_sub, map_mul, map_pow, rho_natCast, rho_subst p hH,
      show (fun t => rho p (F.nthSeries (p ^ v) t)) = fun t => (p : 𝓞) • Hp Fp (p ^ v) t from
        funext fun t => rho_nthSeries Fp hFp0 F hFp _ t,
      subst_smul_family p hHp G]
  have h2 : rho p G = (p : 𝓞) ^ N • φ i - T := by rw [hT, sub_sub_cancel]
  have h3 : rho p (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) =
      (p : MvPowerSeries (Fin d) 𝓞) ^ v * T - subst (Hp Fp (p ^ v)) T := by
    rw [h1, h2, subst_sub hHp, subst_smul hHp, subst_Hp_eq_nsmul Fp hFp0 φ hφ0 hφF, nsmul_eq_mul, Nat.cast_pow,
      mul_sub, mul_smul_comm]
    abel
  rw [h3, map_sub, show ((p : MvPowerSeries (Fin d) 𝓞) ^ v * T) = C ((p : 𝓞) ^ v) * T by
      rw [map_pow, map_natCast], coeff_C_mul, hTcoeff m hm, mul_zero, zero_sub, neg_eq_zero]

  apply coeff_of_lt_order
  have hinf : (1 : ℕ∞) ≤ ⨅ j, (Hp Fp (p ^ v) j).order := by
    refine le_iInf fun j => nat_le_order fun m' hm' => ?_
    have : m' = 0 := (Finsupp.degree_eq_zero_iff m').1 (by exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast hm'))
    rw [this, coeff_zero_eq_constantCoeff_apply, constantCoeff_Hp Fp hFp0]
  calc ((m.degree : ℕ) : ℕ∞) < (p ^ N : ℕ) := by exact_mod_cast hm
    _ ≤ T.order := hTord
    _ ≤ (⨅ j, (Hp Fp (p ^ v) j).order) * T.order := le_mul_of_one_le_left (by simp) hinf
    _ ≤ (T.subst (Hp Fp (p ^ v))).order := le_order_subst hHp T

end Shadow

section Rside

variable {𝓞 : Type*} [CommRing 𝓞] {R : Type*} [CommRing R] [Algebra 𝓞 R] {σ : Type*}

noncomputable def psum (x : σ → R) (T : Finset (σ →₀ ℕ)) (S : MvPowerSeries σ 𝓞) : R :=
  ∑ m ∈ T, coeff m S • m.prod fun s e => x s ^ e

theorem hasEval_of_mem_radical [Finite σ] (J : Ideal R) {x : σ → R} (hx : ∀ s, x s ∈ J.radical) :
    letI : TopologicalSpace R := J.adicTopology
    MvPowerSeries.HasEval x := by
  letI : TopologicalSpace R := J.adicTopology
  refine ⟨fun s => ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hx s
    show Filter.Tendsto (x s ^ ·) Filter.atTop (nhds 0)
    rw [(J.hasBasis_nhds_zero_adic).tendsto_right_iff]
    intro n _
    filter_upwards [Filter.eventually_ge_atTop (k * n)] with m hm
    obtain ⟨r, rfl⟩ : ∃ r, m = k * n + r := ⟨m - k * n, by omega⟩
    rw [pow_add, pow_mul]
    exact SetLike.mem_coe.mpr (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk n))
  · rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot

theorem exists_adicEval_sub_psum_mem [Finite σ] (J : Ideal R) [IsAdicComplete J R] {x : σ → R}
    (hx : ∀ s, x s ∈ J.radical) (S : MvPowerSeries σ 𝓞) (K : ℕ) :
    ∃ T₀ : Finset (σ →₀ ℕ), ∀ T : Finset (σ →₀ ℕ), T₀ ⊆ T →
      MvFormalGroup.adicEval J x S - psum x T S ∈ J ^ K := by
  classical
  letI : UniformSpace 𝓞 := ⊥
  letI : WithIdeal R := ⟨J⟩
  haveI : CompleteSpace R :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J R›).1
  haveI : T2Space R :=
    ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp ‹IsAdicComplete J R›).2
  haveI : ContinuousSMul 𝓞 R := DiscreteTopology.instContinuousSMul 𝓞 R
  have ha : MvPowerSeries.HasEval x := hasEval_of_mem_radical J hx
  have heq : MvFormalGroup.adicEval J x S = MvPowerSeries.aeval ha S := by
    rw [← MvFormalGroup.coe_adicEvalAlgHom J hx]
    rfl
  have hsum := MvPowerSeries.hasSum_aeval ha S
  rw [HasSum] at hsum
  have hev := (J.hasBasis_nhds_adic (MvPowerSeries.aeval ha S)).tendsto_right_iff.1 hsum K trivial
  rw [SummationFilter.unconditional_filter, Filter.eventually_atTop] at hev
  obtain ⟨T₀, hT₀⟩ := hev
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  simp only [Set.mem_image, SetLike.mem_coe] at h
  obtain ⟨z, hz, hzT⟩ := h
  rw [heq, show psum x T S = ∑ m ∈ T, coeff m S • m.prod (fun s e => x s ^ e) from rfl, ← hzT,
    sub_add_cancel_left]
  exact (J ^ K).neg_mem_iff.2 hz

theorem adicEval_mem_pow [Finite σ] (J : Ideal R) [IsAdicComplete J R] {x : σ → R}
    (hx : ∀ s, x s ∈ J.radical) (S : MvPowerSeries σ 𝓞) (K : ℕ)
    (h : ∀ m : σ →₀ ℕ, coeff m S = 0 ∨ (m.prod fun s e => x s ^ e) ∈ J ^ K) :
    MvFormalGroup.adicEval J x S ∈ J ^ K := by
  obtain ⟨T₀, hT₀⟩ := exists_adicEval_sub_psum_mem J hx S K
  have h1 := hT₀ T₀ subset_rfl
  have h2 : psum x T₀ S ∈ J ^ K := by
    refine Ideal.sum_mem _ fun m _ => ?_
    rcases h m with h0 | hmem
    · rw [h0, zero_smul]; exact Ideal.zero_mem _
    · rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ hmem
  have := Ideal.add_mem _ h1 h2
  rwa [sub_add_cancel] at this

omit [Algebra 𝓞 R] in

theorem prod_pow_mem_pow {x : σ → R} {J : Ideal R} {e : ℕ} (hxe : ∀ s, x s ^ e ∈ J) (m : σ →₀ ℕ)
    {s : σ} {K : ℕ} (hs : e * K < m s) : (m.prod fun s k => x s ^ k) ∈ J ^ K := by
  classical
  have hsupp : s ∈ m.support := Finsupp.mem_support_iff.2 (by omega)
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hsupp]
  apply Ideal.mul_mem_right
  rw [show m s = e * K + (m s - e * K) by omega, pow_add, pow_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hxe s) K)

omit [Algebra 𝓞 R] [CommRing R] in

theorem exists_lt_apply [Fintype σ] (m : σ →₀ ℕ) (B : ℕ) (h : Fintype.card σ * B < m.degree) : ∃ s, B < m s := by
  by_contra h'
  have h'' : ∀ s, m s ≤ B := fun s => not_lt.1 (not_exists.1 h' s)
  have : m.degree ≤ Fintype.card σ * B := by
    rw [Finsupp.degree_eq_sum]
    calc ∑ i, m i ≤ ∑ _i : σ, B := Finset.sum_le_sum fun i _ => h'' i
      _ = Fintype.card σ * B := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

omit [Algebra 𝓞 R] [CommRing R] in

theorem exists_N1 {q : ℕ} (hq : 2 ≤ q) (A₀ v : ℕ) : ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → A₀ * (N + v) < q ^ N := by
  refine ⟨(A₀ * (v + 1) + 1) ^ 2 + 1, fun N hN => ?_⟩
  set A := A₀ * (v + 1) + 1 with hA
  have hA1 : 1 ≤ A := by omega
  have hAN : A ≤ N := by nlinarith
  obtain ⟨M, rfl⟩ : ∃ M, N = M + A := ⟨N - A, by omega⟩
  have h1 : A + 1 ≤ 2 ^ A := Nat.lt_two_pow_self
  have h2 : M + 1 ≤ 2 ^ M := Nat.lt_two_pow_self
  have hMA : 1 ≤ M + A := by omega
  calc A₀ * (M + A + v) = A₀ * (M + A) + A₀ * v * 1 := by ring
    _ ≤ A₀ * (M + A) + A₀ * v * (M + A) := Nat.add_le_add_left (Nat.mul_le_mul_left _ hMA) _
    _ < A₀ * (M + A) + A₀ * v * (M + A) + (M + A) := by omega
    _ = A * (M + A) := by rw [hA]; ring
    _ ≤ (M + 1) * (A + 1) := by nlinarith
    _ ≤ 2 ^ M * 2 ^ A := Nat.mul_le_mul h2 h1
    _ = 2 ^ (M + A) := (pow_add 2 M A).symm
    _ ≤ q ^ (M + A) := Nat.pow_le_pow_left hq _

theorem eq_zero_of_natCast_mul_eq_zero [Module.Free 𝓞 R] {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {a : R} (h : (p : R) * a = 0) : a = 0 := by
  classical
  let b := Module.Free.chooseBasis 𝓞 R
  have hrepr : ∀ i, b.repr a i = 0 := by
    intro i
    have h1 : b.repr ((p : R) * a) i = 0 := by rw [h, map_zero, Finsupp.zero_apply]
    have h2 : (p : R) * a = (p : 𝓞) • a := by rw [Algebra.smul_def, map_natCast]
    rw [h2, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    exact (mem_nonZeroDivisors_iff.mp hp).1 _ h1
  have : b.repr a = 0 := Finsupp.ext hrepr
  exact b.repr.map_eq_zero_iff.1 this

theorem eq_zero_of_pow_mul_eq_zero [Module.Free 𝓞 R] {p : ℕ} (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞) :
    ∀ (k : ℕ) {a : R}, (p : R) ^ k * a = 0 → a = 0
  | 0, a, h => by simpa using h
  | k + 1, a, h => by
    rw [pow_succ, mul_assoc] at h
    exact eq_zero_of_natCast_mul_eq_zero hp (eq_zero_of_pow_mul_eq_zero hp k h)

end Rside

section Main

variable {𝓞 : Type*} [CommRing 𝓞] (p : ℕ) [hp : Fact p.Prime] (hpR : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
  {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
  (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
  (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
    (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
  (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
  (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
  (hφ0 : ∀ i, (φ i).constantCoeff = 0)
  (hφ1 : MvFormalGroup.linearPart φ = 1)
  (hφF : ∀ i, subst Fp (φ i) =
    subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
      subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
  (v : ℕ) {R : Type*} [CommRing R] [Algebra 𝓞 R] [Module.Free 𝓞 R]
  [IsAdicComplete (Ideal.span {(p : R)}) R]
  (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R)
  (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
  (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
    π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
  (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))

include hpR hFp hFp0 hφ0 hφ1 hφF hπX hπeval hkerπ in
theorem main :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
          (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
            (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
        π G ∈ Ideal.span {(p : R) ^ N} := by
  classical

  have hint : ∀ (i j : Fin d) (m : Fin d →₀ ℕ),
      ((m j + 1 : ℕ) : 𝓞) * coeff (m + Finsupp.single j 1) (φ i) ∈ Ideal.span {(p : 𝓞) ^ m.degree} :=
    fun i j m => MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
      p hpR F Fp hFp hFp0 φ hφ0 hφ1 hφF i j m

  have hex : ∃ e : ℕ, ∀ s : Fin d, π (X s) ^ e ∈ Ideal.span {(p : R)} := by
    have hπX' : ∀ s : Fin d, ∃ n : ℕ, π (X s) ^ n ∈ Ideal.span {(p : R)} := fun s => hπX s
    choose e he using hπX'
    refine ⟨Finset.univ.sup e, fun s => ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, Finset.univ.sup e = e s + t :=
      ⟨_, (Nat.add_sub_cancel' (Finset.le_sup (f := e) (Finset.mem_univ s))).symm⟩
    rw [ht, pow_add]
    exact Ideal.mul_mem_right _ _ (he s)
  obtain ⟨e, he⟩ := hex
  obtain ⟨N₁, hN₁⟩ := exists_N1 (Nat.Prime.two_le hp.out) (d * e) v
  refine ⟨N₁, fun N hN i G hG => ?_⟩
  set J : Ideal R := Ideal.span {(p : R)} with hJ

  have hE : ∀ m : Fin d →₀ ℕ, m.degree < p ^ N →
      coeff m (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) = 0 :=
    coeff_shadow_eq_zero hpR F Fp hFp hFp0 φ hφ0 hφF hint v N i G hG

  have hH0 : ∀ j, π (F.nthSeries (p ^ v) j) = 0 := fun j => by
    have : F.nthSeries (p ^ v) j ∈ RingHom.ker π := by
      rw [hkerπ]; exact Ideal.subset_span ⟨j, rfl⟩
    exact this
  have hB : π (subst (F.nthSeries (p ^ v)) G) ∈ J ^ (N + v) := by
    rw [hπeval, MvFormalGroup.adicEval_subst J hπX
      (hasSubst_of_constantCoeff_zero (MvFormalGroup.constantCoeff_nthSeries F _))]
    have h0 : (fun t => MvFormalGroup.adicEval J (fun i => π (X i)) (F.nthSeries (p ^ v) t)) =
        fun _ => (0 : R) := by
      funext t; rw [← hπeval, hH0]
    rw [h0]
    apply adicEval_mem_pow J (fun _ => Ideal.zero_mem _) G (N + v)
    intro m
    by_cases hm : m = 0
    · left
      rw [hm, show coeff 0 G = G.coeff 0 from rfl, (hG 0).1 (by simp), show (φ i).coeff 0 = coeff 0 (φ i) from rfl,
        coeff_zero_eq_constantCoeff_apply, hφ0, mul_zero]
    · right
      obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.2 hm
      rw [Finsupp.prod, Finset.prod_eq_zero hs (by rw [zero_pow (Finsupp.mem_support_iff.1 hs)])]
      exact Ideal.zero_mem _

  have hC : π (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) ∈ J ^ (N + v) := by
    rw [hπeval]
    apply adicEval_mem_pow J hπX _ (N + v)
    intro m
    rcases lt_or_ge m.degree (p ^ N) with hlt | hge
    · exact Or.inl (hE m hlt)
    · right
      obtain ⟨s, hs⟩ := exists_lt_apply m (e * (N + v))
        (by rw [Fintype.card_fin, ← mul_assoc]; exact lt_of_lt_of_le (hN₁ N hN) hge)
      exact prod_pow_mem_pow he m hs

  have hD : (p : R) ^ v * π G ∈ J ^ (N + v) := by
    have : (p : R) ^ v * π G = π (subst (F.nthSeries (p ^ v)) G) -
        π (subst (F.nthSeries (p ^ v)) G - (p : MvPowerSeries (Fin d) 𝓞) ^ v * G) := by
      rw [map_sub, map_mul, map_pow, map_natCast]; ring
    rw [this]
    exact Ideal.sub_mem _ hB hC
  rw [hJ, Ideal.span_singleton_pow] at hD
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hD
  refine Ideal.mem_span_singleton'.2 ⟨b, ?_⟩
  have h0 : (p : R) ^ v * (b * (p : R) ^ N - π G) = 0 := by
    rw [mul_sub, sub_eq_zero, mul_left_comm, ← pow_add, add_comm, hb]
  exact sub_eq_zero.1 (eq_zero_of_pow_mul_eq_zero hpR v h0)

end Main

end S17L2d

set_option autoImplicit false

open scoped TensorProduct
open MvPowerSeries

universe u v

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφT : ∀ (N : ℕ) (i : Fin d), ∀ᶠ m in Filter.cofinite, (φ i).coeff m ∈ Ideal.span {(p : 𝓞) ^ N})
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (v : ℕ) (R : Type v) [CommRing R] [HopfAlgebra 𝓞 R] [Module.Free 𝓞 R] [Module.Finite 𝓞 R]
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    [IsAdicComplete (Ideal.span {(p : R ⊗[𝓞] R)}) (R ⊗[𝓞] R)]
    (π : MvPowerSeries (Fin d) 𝓞 →ₐ[𝓞] R) (hπ : Function.Surjective π)
    (hπX : ∀ i, π (X i) ∈ (Ideal.span {(p : R)}).radical)
    (hπeval : ∀ G : MvPowerSeries (Fin d) 𝓞,
      π G = MvFormalGroup.adicEval (Ideal.span {(p : R)}) (fun i => π (X i)) G)
    (hkerπ : RingHom.ker π = Ideal.span (Set.range (F.nthSeries (p ^ v))))
    (hπΔ : ∀ i, Coalgebra.comul (R := 𝓞) (π (X i)) =
      MvFormalGroup.adicEval (Ideal.span {(p : R ⊗[𝓞] R)})
        (Sum.elim (fun j => π (X j) ⊗ₜ[𝓞] (1 : R)) (fun j => (1 : R) ⊗ₜ[𝓞] π (X j)))
        (F.toPowerSeries i))
    (hunip : IsLocalRing (CartierDual (ZMod p) (TensorProduct 𝓞 (ZMod p) R))) :
    ∃ N₁ : ℕ, ∀ N : ℕ, N₁ ≤ N → ∀ (i : Fin d) (G : MvPowerSeries (Fin d) 𝓞),
        (∀ m : Fin d →₀ ℕ,
          (m.degree ≤ N → G.coeff m = (p : 𝓞) ^ (N - m.degree) * (φ i).coeff m) ∧
          (N < m.degree → G.coeff m * (p : 𝓞) ^ (m.degree - N) = (φ i).coeff m ∨
            (G.coeff m = 0 ∧ ¬ (p : 𝓞) ^ (m.degree - N) ∣ (φ i).coeff m))) →
        π G ∈ Ideal.span {(p : R) ^ N} :=
  S17L2d.main p hp F Fp hFp hFp0 φ hφ0 hφ1 hφF v π hπX hπeval hkerπ

end S_Deformation_map_scaledLogTrunc_mem_span_pow_of_mvFormalGroup
end P2MW
export P2MW.S_Deformation_map_scaledLogTrunc_mem_span_pow_of_mvFormalGroup (solution)
