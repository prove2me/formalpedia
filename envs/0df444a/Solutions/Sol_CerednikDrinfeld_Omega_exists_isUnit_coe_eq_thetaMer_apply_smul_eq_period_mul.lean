-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/4dd53058-0bdb-539b-944f-9f82a78a1e9b

import Mathlib
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_holRing_div_eq_theta
import Theorems.Thm_CerednikDrinfeld_Omega_continuous_of_mem_holOn
import Theorems.Thm_CerednikDrinfeld_Omega_exists_blaschke_denominators
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_isAutomorphicWithMultiplier_theta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul

set_option autoImplicit false

open scoped MatrixGroups Topology
open Filter CerednikDrinfeld.Omega

namespace ThetaUnitSol

section Generic

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_eq_one_of_v_sub_one_lt {x : K} {ε : Γ₀} (hx : Valued.v (x - 1) < ε) (hε : ε ≤ 1) :
    Valued.v x = 1 := by
  have h : Valued.v (x - 1) < Valued.v (1 : K) := by rw [map_one]; exact lt_of_lt_of_le hx hε
  have := Valuation.map_add_eq_of_lt_left Valued.v h
  rwa [add_sub_cancel, map_one] at this

theorem ne_zero_of_v_sub_one_lt {x : K} {ε : Γ₀} (hx : Valued.v (x - 1) < ε) (hε : ε ≤ 1) : x ≠ 0 := by
  intro h
  have := v_eq_one_of_v_sub_one_lt hx hε
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem v_mul_sub_one_lt {x y : K} {ε : Γ₀} (hx : Valued.v (x - 1) < ε) (hy : Valued.v (y - 1) < ε)
    (hε : ε ≤ 1) : Valued.v (x * y - 1) < ε := by
  have hx1 := v_eq_one_of_v_sub_one_lt hx hε
  have : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [this]
  refine Valuation.map_add_lt _ ?_ hx
  rw [Valuation.map_mul, hx1, one_mul]
  exact hy

theorem v_inv_sub_one_lt {x : K} {ε : Γ₀} (hx : Valued.v (x - 1) < ε) (hε : ε ≤ 1) :
    Valued.v (x⁻¹ - 1) < ε := by
  have hx1 := v_eq_one_of_v_sub_one_lt hx hε
  have hx0 := ne_zero_of_v_sub_one_lt hx hε
  have : x⁻¹ - 1 = x⁻¹ * (1 - x) := by field_simp
  rw [this, Valuation.map_mul, map_inv₀, hx1, inv_one, one_mul, Valuation.map_sub_swap]
  exact hx

theorem hasProd_inv₀ {ι : Type} {f : ι → K} {a : K} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  show Tendsto (fun s : Finset ι => ∏ i ∈ s, (f i)⁻¹) atTop (𝓝 a⁻¹)
  simp_rw [Finset.prod_inv_distrib]
  exact (show Tendsto (fun s : Finset ι => ∏ i ∈ s, f i) atTop (𝓝 a) from h).inv₀ ha

theorem hasProd_zero_of_eq_zero {ι : Type} {f : ι → K} {i : ι} (hi : f i = 0) : HasProd f 0 := by
  show Tendsto (fun s : Finset ι => ∏ j ∈ s, f j) atTop (𝓝 0)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ({i} : Finset ι)] with s hs
  exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self i)) hi).symm

variable {K₀ : Type} [Field K₀] [Algebra K₀ K] (ϖ : PseudoUniformizer K₀ K)

theorem varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos; rw [h, map_zero] at this; exact lt_irrefl _ this

theorem exists_pow_le_v (hex : IsExhausted ϖ) {y : K} (hy : y ≠ 0) :
    ∃ n : ℕ, Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n ≤ Valued.v y := by
  by_cases hK : y ∈ Set.range (algebraMap K₀ K)
  · obtain ⟨y₀, rfl⟩ := hK
    have hy₀ : y₀ ≠ 0 := fun h => hy (by rw [h, map_zero])
    obtain ⟨N, hN, -⟩ := ϖ.scale y₀ hy₀
    exact ⟨N, hN⟩
  · obtain ⟨n, hn⟩ := hex y hK
    refine ⟨n, ?_⟩
    have := ((mem_affinoid_iff' ϖ n y).1 hn).2 0
    rwa [map_zero, sub_zero] at this

theorem strictAnti_pow_v_varpi : StrictAnti fun N : ℕ => Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N :=
  fun _ _ h => pow_lt_pow_right_of_lt_one₀ ϖ.pos ϖ.lt_one h

theorem tendsto_pow_varpi (hex : IsExhausted ϖ) :
    Tendsto (fun N : ℕ => (algebraMap K₀ K ϖ.ϖ) ^ N) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero K Γ₀).tendsto_right_iff]
  intro γ _
  obtain ⟨x, hx⟩ :=
    MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective (.ofClass (Valued.v (R := K)))
      (γ : MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v (R := K))))
  have hx' : Valued.v.restrict x = γ.1 := by rw [← hx]; rfl
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, map_zero] at hx'
    exact γ.ne_zero hx'.symm
  obtain ⟨n, hn⟩ := exists_pow_le_v ϖ hex hx0
  filter_upwards [eventually_ge_atTop (n + 1)] with N hN
  show Valued.v.restrict ((algebraMap K₀ K ϖ.ϖ) ^ N) < γ.1
  rw [← hx', Valuation.restrict_lt_iff, Valuation.map_pow]
  calc Valued.v (algebraMap K₀ K ϖ.ϖ) ^ N ≤ Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) :=
        (strictAnti_pow_v_varpi ϖ).antitone hN
    _ < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := strictAnti_pow_v_varpi ϖ (Nat.lt_succ_self n)
    _ ≤ Valued.v x := hn

theorem add_pow_mul_mem_affinoid {n : ℕ} {p : K} (hp : p ∈ affinoid ϖ n) {M : ℕ} (hM : 2 * n + 1 ≤ M) :
    p + (algebraMap K₀ K ϖ.ϖ) ^ M * p ∈ affinoid ϖ n := by
  set t := algebraMap K₀ K ϖ.ϖ with ht
  set P := Valued.v t with hP
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact (affinoid_subset_upperHalfPlane ϖ n hp) ⟨0, map_zero _⟩
  have hvp : Valued.v p ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨hp1, hp2⟩ := (mem_affinoid_iff' ϖ n p).1 hp
  have hq : Valued.v (t ^ M * p) = P ^ M * Valued.v p := by rw [Valuation.map_mul, Valuation.map_pow]
  have hM0 : M ≠ 0 := by omega
  have hPM1 : P ^ M < 1 := pow_lt_one₀ zero_le' ϖ.lt_one hM0
  have hlt1 : Valued.v (t ^ M * p) < Valued.v p := by
    rw [hq]
    calc P ^ M * Valued.v p < 1 * Valued.v p := mul_lt_mul_of_pos_right hPM1 (zero_lt_iff.2 hvp)
      _ = Valued.v p := one_mul _
  rw [mem_affinoid_iff']
  constructor
  · rw [Valuation.map_add_eq_of_lt_left _ hlt1]; exact hp1
  · intro a₀
    have hn : n ≤ M := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hk : n < k := by omega
    have hqn : Valued.v (t ^ (n + k) * p) < P ^ n := by
      rw [hq]
      calc P ^ (n + k) * Valued.v p ≤ P ^ (n + k) * P⁻¹ ^ n := mul_le_mul_right hp1 _
        _ = P ^ k := by
            rw [pow_add, mul_comm (P ^ n), mul_assoc, ← mul_pow, mul_inv_cancel₀ ϖ.pos.ne', one_pow, mul_one]
        _ < P ^ n := pow_lt_pow_right_of_lt_one₀ ϖ.pos ϖ.lt_one hk
    have key : Valued.v (t ^ (n + k) * p) < Valued.v (p - algebraMap K₀ K a₀) := lt_of_lt_of_le hqn (hp2 a₀)
    have : p + t ^ (n + k) * p - algebraMap K₀ K a₀ = (p - algebraMap K₀ K a₀) + t ^ (n + k) * p := by ring
    rw [this, Valuation.map_add_eq_of_lt_left _ key]
    exact hp2 a₀

theorem dense_setOf_not_mem (hex : IsExhausted ϖ) (n : ℕ) {O : Set K}
    (hO : {x : K | x ∈ affinoid ϖ n ∧ x ∈ O}.Finite) :
    Dense {w : ↥(affinoid ϖ n) | (w : K) ∉ O} := by
  intro p
  set t := algebraMap K₀ K ϖ.ϖ with ht
  set c := 2 * n + 1 with hc
  have hmem : ∀ N : ℕ, (p : K) + t ^ (N + c) * p ∈ affinoid ϖ n := fun N =>
    add_pow_mul_mem_affinoid ϖ p.2 (by omega)
  let u : ℕ → ↥(affinoid ϖ n) := fun N => ⟨(p : K) + t ^ (N + c) * p, hmem N⟩
  refine mem_closure_of_tendsto (f := u) (b := atTop) ?_ ?_
  · rw [tendsto_subtype_rng]
    show Tendsto (fun N => (p : K) + t ^ (N + c) * p) atTop (𝓝 (p : K))
    have h1 : Tendsto (fun N : ℕ => t ^ N * t ^ c * (p : K)) atTop (𝓝 (0 * t ^ c * p)) :=
      ((tendsto_pow_varpi ϖ hex).mul_const _).mul_const _
    rw [zero_mul, zero_mul] at h1
    have h2 := h1.const_add (p : K)
    rw [add_zero] at h2
    refine h2.congr' (Filter.Eventually.of_forall fun N => ?_)
    simp only [pow_add]
  · have hp0 : (p : K) ≠ 0 := by
      intro h
      exact (affinoid_subset_upperHalfPlane ϖ n p.2) ⟨0, by rw [map_zero, h]⟩
    have hinj : Function.Injective (fun N : ℕ => (p : K) + t ^ (N + c) * p) := by
      intro N M h
      have h' : t ^ (N + c) = t ^ (M + c) := mul_right_cancel₀ hp0 (add_left_cancel h)
      have h'' := congrArg Valued.v h'
      rw [Valuation.map_pow, Valuation.map_pow] at h''
      exact Nat.add_right_cancel ((strictAnti_pow_v_varpi ϖ).injective h'')
    have hfin : ((fun N : ℕ => (p : K) + t ^ (N + c) * p) ⁻¹' {x : K | x ∈ affinoid ϖ n ∧ x ∈ O}).Finite :=
      hO.preimage hinj.injOn
    show ∀ᶠ N in atTop, (u N : K) ∉ O
    rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite]
    refine hfin.subset ?_
    intro N hN
    simp only [Set.mem_setOf_eq, not_not] at hN
    exact ⟨hmem N, hN⟩

theorem unifProd [CompleteSpace K] (hex : IsExhausted ϖ) {S : Set K} {ι : Type} (r : ι → RatPair K)
    (hpf : ∀ γ, (r γ).IsPoleFreeOn S)
    (hbd : ∀ γ, ∃ b : K, ∀ z ∈ S, Valued.v ((r γ).evalAt z) ≤ Valued.v b)
    (h1 : ∀ c : K, c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ S, Valued.v ((r γ).evalAt z - 1) < Valued.v c) :
    ∃ P : ↥S → K, P ∈ holOn K S ∧
      (∀ z : ↥S, HasProd (fun γ => (r γ).evalAt (z : K)) (P z)) ∧
      (∀ z : ↥S, P z = 0 ↔ ∃ γ, (r γ).evalAt (z : K) = 0) := by
  classical
  set t := algebraMap K₀ K ϖ.ϖ with ht_def
  have ht : ∀ k : ℕ, t ^ k ≠ 0 := fun k => pow_ne_zero k (varpi_ne_zero ϖ)
  have hcof : ∀ y : K, y ≠ 0 → ∃ k, Valued.v (t ^ k) ≤ Valued.v y := fun y hy => by
    simp_rw [Valuation.map_pow]; exact exists_pow_le_v ϖ hex hy
  let F : ℕ → Finset ι := fun k => (Filter.eventually_cofinite.1 (h1 (t ^ k) (ht k))).toFinset
  let E : ℕ → Finset ι := fun k => (Finset.range (k + 1)).biUnion F
  refine CerednikDrinfeld.Omega.exists_mem_holOn_hasProd_evalAt K r hpf hbd (fun k => t ^ k) ht hcof E ?_ ?_
  · intro k l hkl
    exact Finset.biUnion_subset_biUnion_of_subset_left F (Finset.range_mono (Nat.succ_le_succ hkl))
  · intro k γ hγ z hz
    have hγF : γ ∉ F k := fun h => hγ (Finset.subset_biUnion_of_mem F (Finset.self_mem_range_succ k) h)
    rw [Set.Finite.mem_toFinset] at hγF
    simp only [Set.mem_setOf_eq, not_not] at hγF
    exact hγF z hz

theorem exists_bound_inv {S : Set K} (D : Polynomial K)
    (h0 : ∃ b : K, ∀ z ∈ S, Valued.v ((z - 0) / D.eval z) ≤ Valued.v b)
    (h1 : ∃ b : K, ∀ z ∈ S, Valued.v ((z - 1) / D.eval z) ≤ Valued.v b) :
    ∃ b : K, ∀ z ∈ S, Valued.v ((D.eval z)⁻¹) ≤ Valued.v b := by
  obtain ⟨b₀, hb₀⟩ := h0
  obtain ⟨b₁, hb₁⟩ := h1
  obtain ⟨B, -, hB₀, hB₁, -⟩ := exists_bound b₀ b₁
  refine ⟨B, fun z hz => ?_⟩
  have : (D.eval z)⁻¹ = (z - 0) / D.eval z - (z - 1) / D.eval z := by
    rw [← sub_div, show (z - 0) - (z - 1) = (1 : K) by ring, one_div]
  rw [this]
  exact (Valuation.map_sub _ _ _).trans (max_le ((hb₀ z hz).trans hB₀) ((hb₁ z hz).trans hB₁))

theorem exists_bound_linear_div {S : Set K} (D₁ D₂ : Polynomial K) (h1 : D₁.natDegree ≤ 1)
    (hz : ∃ b : K, ∀ z ∈ S, Valued.v ((z - 0) / D₂.eval z) ≤ Valued.v b)
    (hinv : ∃ b : K, ∀ z ∈ S, Valued.v ((D₂.eval z)⁻¹) ≤ Valued.v b) :
    ∃ B : K, ∀ z ∈ S, Valued.v (D₁.eval z / D₂.eval z) ≤ Valued.v B := by
  obtain ⟨b₀, hb₀⟩ := hz
  obtain ⟨b₁, hb₁⟩ := hinv
  obtain ⟨B, -, hB₁, hB₂, -⟩ := exists_bound (D₁.coeff 1 * b₀) (D₁.coeff 0 * b₁)
  refine ⟨B, fun z hzS => ?_⟩
  have hD : D₁.eval z = D₁.coeff 1 * z + D₁.coeff 0 := by
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one h1]
    simp
  rw [hD, add_div, mul_div_assoc, div_eq_mul_inv (D₁.coeff 0)]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rw [Valuation.map_mul]
    have h := hb₀ z hzS
    rw [sub_zero] at h
    refine (mul_le_mul_right h _).trans ?_
    rw [← Valuation.map_mul]; exact hB₁
  · rw [Valuation.map_mul]
    refine (mul_le_mul_right (hb₁ z hzS) _).trans ?_
    rw [← Valuation.map_mul]; exact hB₂

theorem bound_scaled {S : Set K} (D : Polynomial K) (κ w' : K)
    (h : ∃ b : K, ∀ z ∈ S, Valued.v ((z - w') / D.eval z) ≤ Valued.v b) :
    ∃ b : K, ∀ z ∈ S, Valued.v ((z - w') / (Polynomial.C κ * D).eval z) ≤ Valued.v b := by
  obtain ⟨b, hb⟩ := h
  refine ⟨b * κ⁻¹, fun z hz => ?_⟩
  rw [Polynomial.eval_mul, Polynomial.eval_C, mul_comm κ, ← div_div, div_eq_mul_inv _ κ, Valuation.map_mul,
    Valuation.map_mul]
  exact mul_le_mul_left (hb z hz) _

end Generic

section Families

variable {K : Type} [Field K] {G : Type}

noncomputable def eFam [Group G] (w : G → K) (d : G → Polynomial K) (z₀ : K) (α γ : G) : RatPair K :=
  ⟨Polynomial.C (z₀ - w (γ * α)) * d γ, Polynomial.C (z₀ - w γ) * d (γ * α)⟩

noncomputable def eFam' [Group G] (w : G → K) (d : G → Polynomial K) (z₀ : K) (α γ : G) : RatPair K :=
  ⟨Polynomial.C (z₀ - w γ) * d (γ * α), Polynomial.C (z₀ - w (γ * α)) * d γ⟩

noncomputable def fFam (w : G → K) (d : G → Polynomial K) (γ : G) : RatPair K :=
  ⟨Polynomial.X - Polynomial.C (w γ), d γ⟩

theorem eFam_evalAt [Group G] (w : G → K) (d : G → Polynomial K) (z₀ : K) (α γ : G) (z : K) :
    (eFam w d z₀ α γ).evalAt z = ((z₀ - w (γ * α)) * (d γ).eval z) / ((z₀ - w γ) * (d (γ * α)).eval z) := by
  simp [eFam, RatPair.evalAt, Polynomial.eval_mul]

theorem eFam'_evalAt [Group G] (w : G → K) (d : G → Polynomial K) (z₀ : K) (α γ : G) (z : K) :
    (eFam' w d z₀ α γ).evalAt z = ((eFam w d z₀ α γ).evalAt z)⁻¹ := by
  rw [eFam_evalAt, inv_div]
  simp [eFam', RatPair.evalAt, Polynomial.eval_mul]

theorem fFam_evalAt (w : G → K) (d : G → Polynomial K) (γ : G) (z : K) :
    (fFam w d γ).evalAt z = (z - w γ) / (d γ).eval z := by
  simp [fFam, RatPair.evalAt]

end Families

section Geometry

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {G : Type} [Group G]

theorem pmoebius_mul_apply (ρ : G →* PGL(2, K₀)) {a : K} (ha : a ∈ upperHalfPlane K₀ K) (γ δ : G) :
    pmoebius K₀ (ρ (γ * δ)) a = pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ δ) a) := by
  rw [map_mul, pmoebius_mul K₀ ha]

theorem exists_orbit_iff (ρ : G →* PGL(2, K₀)) {a : K} (ha : a ∈ upperHalfPlane K₀ K) (α : G) (z : K) :
    (∃ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a) = z) ↔ ∃ γ : G, pmoebius K₀ (ρ γ) a = z := by
  constructor
  · rintro ⟨γ, h⟩
    exact ⟨γ * α, by rw [pmoebius_mul_apply ρ ha]; exact h⟩
  · rintro ⟨γ, h⟩
    refine ⟨γ * α⁻¹, ?_⟩
    rw [← pmoebius_mul_apply ρ ha, mul_assoc, inv_mul_cancel, mul_one]
    exact h

theorem not_exists_orbit_pmoebius (ρ : G →* PGL(2, K₀)) {a z : K} (ha : a ∈ upperHalfPlane K₀ K)
    (hz : z ∈ upperHalfPlane K₀ K) (hoff : ¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = z) (β : G) :
    ¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = pmoebius K₀ (ρ β) z := by
  rintro ⟨γ, h⟩
  apply hoff
  refine ⟨β⁻¹ * γ, ?_⟩
  rw [pmoebius_mul_apply ρ ha, h, ← pmoebius_mul K₀ hz, ← map_mul, inv_mul_cancel, map_one, pmoebius_one]

theorem finite_orbit_mem_affinoid (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ) {a : K} (ha : a ∈ upperHalfPlane K₀ K) (n : ℕ) :
    {γ : G | pmoebius K₀ (ρ γ) a ∈ affinoid ϖ n}.Finite := by
  obtain ⟨m, hm⟩ := hex a ha
  have hsub : {γ : G | pmoebius K₀ (ρ γ) a ∈ affinoid ϖ n} ⊆
      {γ : G | pmoebius K₀ (ρ γ) a ∈ affinoid ϖ (max n m)} :=
    fun γ hγ => affinoid_mono ϖ (le_max_left n m) hγ
  exact (finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ (max n m) (affinoid_mono ϖ (le_max_right n m) hm)).subset hsub

variable [CompleteSpace K] (ϖ : PseudoUniformizer K₀ K) (ρ : G →* PGL(2, K₀))

theorem level_f (hex : IsExhausted ϖ) (d : G → Polynomial K) {a : K}
    (hd2 : ∀ γ : G, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0)
    (hd3 : ∀ (n : ℕ) (γ : G) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - w') / (d γ).eval z) ≤ Valued.v b)
    (hd4 : ∀ (n : ℕ) (c : K), c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - pmoebius K₀ (ρ γ) a) / (d γ).eval z - 1) < Valued.v c) (n : ℕ) :
    ∃ P : ↥(affinoid ϖ n) → K, P ∈ holOn K (affinoid ϖ n) ∧
      (∀ z : ↥(affinoid ϖ n), HasProd (fun γ => (fFam (fun γ => pmoebius K₀ (ρ γ) a) d γ).evalAt (z : K)) (P z)) ∧
      (∀ z : ↥(affinoid ϖ n), P z = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) a = z) := by
  obtain ⟨P, hP, hprod, hzero⟩ := unifProd ϖ hex (S := affinoid ϖ n) (fFam (fun γ => pmoebius K₀ (ρ γ) a) d)
    (fun γ z hz => hd2 γ z (affinoid_subset_upperHalfPlane ϖ n hz))
    (fun γ => by simp_rw [fFam_evalAt]; exact hd3 n γ _)
    (fun c hc => by simp_rw [fFam_evalAt]; exact hd4 n c hc)
  refine ⟨P, hP, hprod, fun z => (hzero z).trans ?_⟩
  simp_rw [fFam_evalAt, div_eq_zero_iff, (hd2 _ (z : K) (affinoid_subset_upperHalfPlane ϖ n z.2)), or_false,
    sub_eq_zero, eq_comm]

omit [CompleteSpace K] in

theorem est_e (hex : IsExhausted ϖ) (hρ : IsDiscrete K ρ) {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) (d : G → Polynomial K)
    (hd2 : ∀ γ : G, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0)
    (hd4 : ∀ (n : ℕ) (c : K), c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - pmoebius K₀ (ρ γ) a) / (d γ).eval z - 1) < Valued.v c)
    (n : ℕ) (c : K) (hc : c ≠ 0) (hc1 : Valued.v c ≤ 1) :
    ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α γ).evalAt z - 1) < Valued.v c := by
  have hbΩ : pmoebius K₀ (ρ α) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha (ρ α)
  obtain ⟨na, hna⟩ := hex a ha
  obtain ⟨nb, hnb⟩ := hex _ hbΩ
  obtain ⟨nz, hnz⟩ := hex z₀ hz₀
  have hnN : n ≤ max (max n na) (max nb nz) := (le_max_left _ _).trans (le_max_left _ _)
  have haN : a ∈ affinoid ϖ (max (max n na) (max nb nz)) :=
    affinoid_mono ϖ ((le_max_right _ _).trans (le_max_left _ _)) hna
  have hbN : pmoebius K₀ (ρ α) a ∈ affinoid ϖ (max (max n na) (max nb nz)) :=
    affinoid_mono ϖ ((le_max_left _ _).trans (le_max_right _ _)) hnb
  have hzN : z₀ ∈ affinoid ϖ (max (max n na) (max nb nz)) :=
    affinoid_mono ϖ ((le_max_right _ _).trans (le_max_right _ _)) hnz
  have hε : Valued.v c ≠ 0 := fun h => hc ((Valuation.zero_iff _).1 h)
  have hT := eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt ϖ ρ hρ _ haN hbN hzN
    (Valued.v c) hε
  have hA := hd4 n c hc
  have hmulR : Tendsto (fun γ : G => γ * α) cofinite cofinite := (mul_left_injective α).tendsto_cofinite
  have hB : ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - pmoebius K₀ (ρ (γ * α)) a) / (d (γ * α)).eval z - 1) < Valued.v c :=
    hmulR.eventually hA
  have hFa : ∀ᶠ γ in cofinite, pmoebius K₀ (ρ γ) a ∉ affinoid ϖ n := by
    rw [Filter.eventually_cofinite]
    simp only [not_not]
    exact finite_orbit_mem_affinoid ϖ hex ρ hρ ha n
  have hFb : ∀ᶠ γ in cofinite, pmoebius K₀ (ρ (γ * α)) a ∉ affinoid ϖ n := hmulR.eventually hFa
  filter_upwards [hT, hA, hB, hFa, hFb] with γ h1 h2 h3 h4 h5
  intro z hz
  have hzΩ : z ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hz
  have hx1 := h1 z (affinoid_mono ϖ hnN hz)
  have hx2 := h2 z hz
  have hx3 := h3 z hz
  have hza : z - pmoebius K₀ (ρ γ) a ≠ 0 := sub_ne_zero.2 fun h => h4 (h ▸ hz)
  have hzb : z - pmoebius K₀ (ρ (γ * α)) a ≠ 0 := sub_ne_zero.2 fun h => h5 (h ▸ hz)
  have hdγ : (d γ).eval z ≠ 0 := hd2 γ z hzΩ
  have hdγα : (d (γ * α)).eval z ≠ 0 := hd2 _ z hzΩ
  have h0a : z₀ - pmoebius K₀ (ρ γ) a ≠ 0 := sub_ne_zero.2 fun h => hz₀a γ h.symm
  have h0b : z₀ - pmoebius K₀ (ρ (γ * α)) a ≠ 0 := sub_ne_zero.2 fun h => hz₀a _ h.symm
  have hid : (eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α γ).evalAt z =
      thetaFactor ρ a (pmoebius K₀ (ρ α) a) z₀ z γ * ((z - pmoebius K₀ (ρ γ) a) / (d γ).eval z)⁻¹ *
        ((z - pmoebius K₀ (ρ (γ * α)) a) / (d (γ * α)).eval z) := by
    rw [eFam_evalAt, thetaFactor, crossRatio, ← pmoebius_mul_apply ρ ha]
    field_simp
  rw [hid]
  exact v_mul_sub_one_lt (v_mul_sub_one_lt hx1 (v_inv_sub_one_lt hx2 hc1) hc1) hx3 hc1

theorem level_e (hex : IsExhausted ϖ) (hρ : IsDiscrete K ρ) {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) (d : G → Polynomial K)
    (hd1 : ∀ γ : G, (d γ).natDegree ≤ 1)
    (hd2 : ∀ γ : G, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0)
    (hd3 : ∀ (n : ℕ) (γ : G) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - w') / (d γ).eval z) ≤ Valued.v b)
    (hd4 : ∀ (n : ℕ) (c : K), c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - pmoebius K₀ (ρ γ) a) / (d γ).eval z - 1) < Valued.v c) (n : ℕ) :
    ∃ P : ↥(affinoid ϖ n) → K, P ∈ holOn K (affinoid ϖ n) ∧
      (∀ z : ↥(affinoid ϖ n),
        HasProd (fun γ => (eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α γ).evalAt (z : K)) (P z)) ∧
      (∀ z : ↥(affinoid ϖ n), P z ≠ 0) := by
  have h0 : ∀ γ : G, z₀ - pmoebius K₀ (ρ γ) a ≠ 0 := fun γ => sub_ne_zero.2 fun h => hz₀a γ h.symm
  have hΩ : affinoid ϖ n ⊆ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n
  obtain ⟨P, hP, hprod, hzero⟩ := unifProd ϖ hex (S := affinoid ϖ n) (eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α)
    (fun γ z hz => by
      simp only [eFam, Polynomial.eval_mul, Polynomial.eval_C]
      exact mul_ne_zero (h0 γ) (hd2 _ z (hΩ hz)))
    (fun γ => by
      have hz' : ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - 0) /
          (Polynomial.C (z₀ - pmoebius K₀ (ρ γ) a) * d (γ * α)).eval z) ≤ Valued.v b :=
        bound_scaled _ _ _ (hd3 n (γ * α) 0)
      have h1' : ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - 1) /
          (Polynomial.C (z₀ - pmoebius K₀ (ρ γ) a) * d (γ * α)).eval z) ≤ Valued.v b :=
        bound_scaled _ _ _ (hd3 n (γ * α) 1)
      exact exists_bound_linear_div (S := affinoid ϖ n) _ _
        ((Polynomial.natDegree_C_mul_le _ _).trans (hd1 γ)) hz' (exists_bound_inv _ hz' h1'))
    (fun c hc => by
      by_cases hc1 : Valued.v c ≤ 1
      · exact est_e ϖ ρ hex hρ ha hz₀ hz₀a α d hd2 hd4 n c hc hc1
      · have h := est_e ϖ ρ hex hρ ha hz₀ hz₀a α d hd2 hd4 n 1 one_ne_zero (le_of_eq (map_one _))
        filter_upwards [h] with γ hγ z hz
        exact (hγ z hz).trans (by rw [map_one]; exact lt_of_not_ge hc1))
  refine ⟨P, hP, hprod, fun z hz0 => ?_⟩
  obtain ⟨γ, hγ⟩ := (hzero z).1 hz0
  rw [eFam_evalAt] at hγ
  exact div_ne_zero (mul_ne_zero (h0 _) (hd2 _ _ (hΩ z.2))) (mul_ne_zero (h0 _) (hd2 _ _ (hΩ z.2))) hγ

theorem level_e' (hex : IsExhausted ϖ) (hρ : IsDiscrete K ρ) {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) (d : G → Polynomial K)
    (hd1 : ∀ γ : G, (d γ).natDegree ≤ 1)
    (hd2 : ∀ γ : G, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0)
    (hd3 : ∀ (n : ℕ) (γ : G) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - w') / (d γ).eval z) ≤ Valued.v b)
    (hd4 : ∀ (n : ℕ) (c : K), c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - pmoebius K₀ (ρ γ) a) / (d γ).eval z - 1) < Valued.v c) (n : ℕ) :
    ∃ P : ↥(affinoid ϖ n) → K, P ∈ holOn K (affinoid ϖ n) ∧
      (∀ z : ↥(affinoid ϖ n),
        HasProd (fun γ => ((eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α γ).evalAt (z : K))⁻¹) (P z)) := by
  have h0 : ∀ γ : G, z₀ - pmoebius K₀ (ρ γ) a ≠ 0 := fun γ => sub_ne_zero.2 fun h => hz₀a γ h.symm
  have hΩ : affinoid ϖ n ⊆ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n
  obtain ⟨P, hP, hprod, -⟩ := unifProd ϖ hex (S := affinoid ϖ n) (eFam' (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α)
    (fun γ z hz => by
      simp only [eFam', Polynomial.eval_mul, Polynomial.eval_C]
      exact mul_ne_zero (h0 _) (hd2 _ z (hΩ hz)))
    (fun γ => by
      have hz' : ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - 0) /
          (Polynomial.C (z₀ - pmoebius K₀ (ρ (γ * α)) a) * d γ).eval z) ≤ Valued.v b :=
        bound_scaled _ _ _ (hd3 n γ 0)
      have h1' : ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((z - 1) /
          (Polynomial.C (z₀ - pmoebius K₀ (ρ (γ * α)) a) * d γ).eval z) ≤ Valued.v b :=
        bound_scaled _ _ _ (hd3 n γ 1)
      exact exists_bound_linear_div (S := affinoid ϖ n) _ _
        ((Polynomial.natDegree_C_mul_le _ _).trans (hd1 _)) hz' (exists_bound_inv _ hz' h1'))
    (fun c hc => by
      by_cases hc1 : Valued.v c ≤ 1
      · filter_upwards [est_e ϖ ρ hex hρ ha hz₀ hz₀a α d hd2 hd4 n c hc hc1] with γ hγ z hz
        rw [eFam'_evalAt]
        exact v_inv_sub_one_lt (hγ z hz) hc1
      · have h := est_e ϖ ρ hex hρ ha hz₀ hz₀a α d hd2 hd4 n 1 one_ne_zero (le_of_eq (map_one _))
        filter_upwards [h] with γ hγ z hz
        rw [eFam'_evalAt]
        exact (v_inv_sub_one_lt (hγ z hz) (le_of_eq (map_one _))).trans
          (by rw [map_one]; exact lt_of_not_ge hc1))
  refine ⟨P, hP, fun z => ?_⟩
  have := hprod z
  simp_rw [eFam'_evalAt] at this
  exact this

theorem core (hex : IsExhausted ϖ) (hρ : IsDiscrete K ρ) {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) :
    ∃ e f : G → K → K,
      (fun z : ↥(upperHalfPlane K₀ K) => ∏' γ, e γ z) ∈ holRing ϖ ∧
      (fun z : ↥(upperHalfPlane K₀ K) => ∏' γ, (e γ z)⁻¹) ∈ holRing ϖ ∧
      (∀ z ∈ upperHalfPlane K₀ K, HasProd (fun γ => e γ z) (∏' γ, e γ z)) ∧
      (∀ z ∈ upperHalfPlane K₀ K, HasProd (fun γ => (e γ z)⁻¹) (∏' γ, (e γ z)⁻¹)) ∧
      (∀ z ∈ upperHalfPlane K₀ K, ∀ γ, e γ z ≠ 0) ∧
      (∀ z ∈ upperHalfPlane K₀ K, ∃ A : K, HasProd (fun γ => f γ z) A ∧
        (A = 0 ↔ ∃ γ : G, pmoebius K₀ (ρ γ) a = z)) ∧
      (∀ z ∈ upperHalfPlane K₀ K, (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = z) → ∀ γ : G,
        thetaFactor ρ a (pmoebius K₀ (ρ α) a) z₀ z γ = e γ z * f γ z * (f (γ * α) z)⁻¹) := by
  have hw : ∀ γ : G, pmoebius K₀ (ρ γ) a ∈ upperHalfPlane K₀ K := fun γ => pmoebius_mem_upperHalfPlane K₀ ha (ρ γ)
  obtain ⟨d, hd1, hd2, hd3, hd4⟩ := exists_blaschke_denominators K₀ K ϖ hex (fun γ => pmoebius K₀ (ρ γ) a) hw
    (finite_orbit_mem_affinoid ϖ hex ρ hρ ha)
  have h0 : ∀ γ : G, z₀ - pmoebius K₀ (ρ γ) a ≠ 0 := fun γ => sub_ne_zero.2 fun h => hz₀a γ h.symm
  refine ⟨fun γ z => (eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α γ).evalAt z,
    fun γ z => (fFam (fun γ => pmoebius K₀ (ρ γ) a) d γ).evalAt z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    obtain ⟨P, hP, hprod, -⟩ := level_e ϖ ρ hex hρ ha hz₀ hz₀a α d hd1 hd2 hd3 hd4 n
    have : restrictAffinoid ϖ n (fun z : ↥(upperHalfPlane K₀ K) =>
        ∏' γ, (eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α γ).evalAt z) = P :=
      funext fun z => (hprod z).tprod_eq
    rw [this]
    exact hP
  · intro n
    obtain ⟨P, hP, hprod⟩ := level_e' ϖ ρ hex hρ ha hz₀ hz₀a α d hd1 hd2 hd3 hd4 n
    have : restrictAffinoid ϖ n (fun z : ↥(upperHalfPlane K₀ K) =>
        ∏' γ, ((eFam (fun γ => pmoebius K₀ (ρ γ) a) d z₀ α γ).evalAt z)⁻¹) = P :=
      funext fun z => (hprod z).tprod_eq
    rw [this]
    exact hP
  · intro z hz
    obtain ⟨n, hn⟩ := hex z hz
    obtain ⟨P, -, hprod, -⟩ := level_e ϖ ρ hex hρ ha hz₀ hz₀a α d hd1 hd2 hd3 hd4 n
    exact (hprod ⟨z, hn⟩).multipliable.hasProd
  · intro z hz
    obtain ⟨n, hn⟩ := hex z hz
    obtain ⟨P, -, hprod⟩ := level_e' ϖ ρ hex hρ ha hz₀ hz₀a α d hd1 hd2 hd3 hd4 n
    exact (hprod ⟨z, hn⟩).multipliable.hasProd
  · intro z hz γ
    beta_reduce
    rw [eFam_evalAt]
    exact div_ne_zero (mul_ne_zero (h0 _) (hd2 _ _ hz)) (mul_ne_zero (h0 _) (hd2 _ _ hz))
  · intro z hz
    obtain ⟨n, hn⟩ := hex z hz
    obtain ⟨P, -, hprod, hzero⟩ := level_f ϖ ρ hex d hd2 hd3 hd4 n
    exact ⟨P ⟨z, hn⟩, hprod ⟨z, hn⟩, hzero ⟨z, hn⟩⟩
  · intro z hz hzo γ
    have hza : z - pmoebius K₀ (ρ γ) a ≠ 0 := sub_ne_zero.2 fun h => hzo ⟨γ, h.symm⟩
    have hzb : z - pmoebius K₀ (ρ (γ * α)) a ≠ 0 := sub_ne_zero.2 fun h => hzo ⟨γ * α, h.symm⟩
    have hdγ : (d γ).eval z ≠ 0 := hd2 γ z hz
    have hdγα : (d (γ * α)).eval z ≠ 0 := hd2 _ z hz
    have h0a := h0 γ
    have h0b := h0 (γ * α)
    beta_reduce
    rw [eFam_evalAt, fFam_evalAt, fFam_evalAt, thetaFactor, crossRatio, ← pmoebius_mul_apply ρ ha]
    field_simp

end Geometry

end ThetaUnitSol

open ThetaUnitSol in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (α : G) :
    ∃ U : ↥(holRing ϖ), IsUnit U ∧
      algebraMap ↥(holRing ϖ) (merField ϖ) U = thetaMer ϖ ρ a (pmoebius K₀ (ρ α) a) z₀ ∧
      (∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
        (U : ↥(upperHalfPlane K₀ K) → K) z = theta ρ a (pmoebius K₀ (ρ α) a) z₀ (z : K)) ∧
      ∀ (β : G) (z : ↥(upperHalfPlane K₀ K)),
        (U : ↥(upperHalfPlane K₀ K) → K) ((ρ β) • z) = period ρ a z₀ α β * (U : ↥(upperHalfPlane K₀ K) → K) z := by
  obtain ⟨e, f, hU, hV, hUprod, hVprod, hne, hf, hid⟩ := ThetaUnitSol.core ϖ ρ hex hρ ha hz₀ hz₀a α

  set U₀ : ↥(upperHalfPlane K₀ K) → K := fun z => ∏' γ, e γ z with hU₀_def
  set V₀ : ↥(upperHalfPlane K₀ K) → K := fun z => ∏' γ, (e γ z)⁻¹ with hV₀_def
  let Uh : ↥(holRing ϖ) := ⟨U₀, hU⟩
  let Vh : ↥(holRing ϖ) := ⟨V₀, hV⟩
  have hUV : Uh * Vh = 1 := by
    apply Subtype.ext
    funext z
    show U₀ z * V₀ z = 1
    have h1 : HasProd (fun γ => e γ z * (e γ z)⁻¹) (U₀ z * V₀ z) := (hUprod z z.2).mul (hVprod z z.2)
    have h2 : HasProd (fun γ => e γ z * (e γ z)⁻¹) 1 := by
      have : (fun γ => e γ (z : K) * (e γ z)⁻¹) = fun _ => 1 := funext fun γ => mul_inv_cancel₀ (hne z z.2 γ)
      rw [this]
      exact hasProd_one
    exact h1.unique h2

  have hbΩ : pmoebius K₀ (ρ α) a ∈ upperHalfPlane K₀ K := pmoebius_mem_upperHalfPlane K₀ ha (ρ α)
  have hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a) ≠ z₀ := fun γ h =>
    hz₀a (γ * α) (by rw [pmoebius_mul_apply ρ ha]; exact h)

  have hoff : ∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
      HasProd (fun γ => thetaFactor ρ a (pmoebius K₀ (ρ α) a) z₀ z γ) (U₀ z) := by
    intro z hzo
    obtain ⟨A, hA, hA0⟩ := hf z z.2
    have hAne : A ≠ 0 := fun h => hzo (hA0.1 h)
    have hA' : HasProd (fun γ => f (γ * α) z) A := (Equiv.hasProd_iff (Equiv.mulRight α)).2 hA
    have h := ((hUprod z z.2).mul hA).mul (hasProd_inv₀ hA' hAne)
    rw [mul_assoc, mul_inv_cancel₀ hAne, mul_one] at h
    have hfun : (fun γ => thetaFactor ρ a (pmoebius K₀ (ρ α) a) z₀ z γ) =
        fun γ => e γ z * f γ z * (f (γ * α) z)⁻¹ := funext fun γ => hid z z.2 hzo γ
    rw [hfun]
    exact h
  have htheta : ∀ z : ↥(upperHalfPlane K₀ K), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
      theta ρ a (pmoebius K₀ (ρ α) a) z₀ z = U₀ z := fun z hzo => (hoff z hzo).tprod_eq

  have hmult : ∀ z ∈ upperHalfPlane K₀ K, ThetaMultipliable ρ a (pmoebius K₀ (ρ α) a) z₀ z := by
    intro z hz
    by_cases hzo : ∃ γ : G, pmoebius K₀ (ρ γ) a = z
    · obtain ⟨γ, hγ⟩ := hzo
      refine (hasProd_zero_of_eq_zero (i := γ) ?_).multipliable
      simp [thetaFactor, crossRatio, hγ]
    · exact (hoff ⟨z, hz⟩ hzo).multipliable

  obtain ⟨cm, hcm, haut⟩ := exists_monoidHom_isAutomorphicWithMultiplier_theta ρ ha hbΩ hz₀ hz₀a hz₀b hmult
  have hautU : ∀ (β : G) (z : ↥(upperHalfPlane K₀ K)), (¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (z : K)) →
      U₀ ((ρ β) • z) = period ρ a z₀ α β * U₀ z := by
    intro β z hzo
    have hβz : ¬ ∃ γ : G, pmoebius K₀ (ρ γ) a = (((ρ β) • z : ↥(upperHalfPlane K₀ K)) : K) :=
      not_exists_orbit_pmoebius ρ ha z.2 hzo β
    rw [← htheta _ hβz, ← htheta z hzo, coe_smul_upperHalfPlane, haut β z z.2, hcm β]
    rfl
  refine ⟨Uh, ⟨⟨Uh, Vh, hUV, by rw [mul_comm]; exact hUV⟩, rfl⟩, ?_, fun z hzo => (htheta z hzo).symm, ?_⟩
  ·
    obtain ⟨F, H, hH, hHz, hFz, hFH⟩ :=
      exists_holRing_div_eq_theta K₀ K ϖ hex ρ hρ ha hbΩ hz₀ hz₀a hz₀b
    have hex' : ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a (pmoebius K₀ (ρ α) a) z₀ F H :=
      ⟨F, H, hH, hHz, hFz, hFH⟩
    rw [thetaMer_def_of_exists ϖ ρ a _ z₀ hex']
    obtain ⟨hH', hHz', hFz', hFH'⟩ := hex'.choose_spec.choose_spec
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul]
    apply Subtype.ext
    funext z
    rw [Subring.coe_mul, Pi.mul_apply]
    show (hex'.choose_spec.choose : ↥(upperHalfPlane K₀ K) → K) z * U₀ z =
      (hex'.choose : ↥(upperHalfPlane K₀ K) → K) z
    by_cases hzo : ∃ γ : G, pmoebius K₀ (ρ γ) a = z
    · have hH0 : (hex'.choose_spec.choose : ↥(upperHalfPlane K₀ K) → K) z = 0 :=
        (hHz' z).2 ((exists_orbit_iff ρ ha α z).2 hzo)
      have hF0 : (hex'.choose : ↥(upperHalfPlane K₀ K) → K) z = 0 := (hFz' z).2 hzo
      rw [hH0, hF0, zero_mul]
    · have hzb : ¬ ∃ γ : G, pmoebius K₀ (ρ γ) (pmoebius K₀ (ρ α) a) = z :=
        fun h => hzo ((exists_orbit_iff ρ ha α z).1 h)
      have hH0 : (hex'.choose_spec.choose : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 :=
        fun h => hzb ((hHz' z).1 h)
      have h := hFH' z hzb
      rw [htheta z hzo, div_eq_iff hH0] at h
      rw [mul_comm]
      exact h.symm
  ·
    intro β z
    by_cases hzo : ∃ γ : G, pmoebius K₀ (ρ γ) a = z
    · obtain ⟨n, hn⟩ := hex (z : K) z.2
      set g₁ : ↥(affinoid ϖ n) → K :=
        restrictAffinoid ϖ n (((ρ β)⁻¹ • Uh : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) with hg₁_def
      set g₂ : ↥(affinoid ϖ n) → K := restrictAffinoid ϖ n
        ((algebraMap K ↥(holRing ϖ) (period ρ a z₀ α β) * Uh : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K)
        with hg₂_def
      have hg₁ : g₁ ∈ holOn K (affinoid ϖ n) := ((ρ β)⁻¹ • Uh).2 n
      have hg₂ : g₂ ∈ holOn K (affinoid ϖ n) := (algebraMap K ↥(holRing ϖ) (period ρ a z₀ α β) * Uh).2 n
      have hg₁v : ∀ w : ↥(affinoid ϖ n),
          g₁ w = U₀ ((ρ β) • Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) w) := fun w => by
        rw [hg₁_def, restrictAffinoid, Function.comp_apply, coe_smul_holRing_apply, inv_inv]
      have hg₂v : ∀ w : ↥(affinoid ϖ n),
          g₂ w = period ρ a z₀ α β * U₀ (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) w) := fun w => by
        rw [hg₂_def, restrictAffinoid, Function.comp_apply, Subring.coe_mul, Pi.mul_apply, algebraMap_holRing_apply]
      have hD : Dense {w : ↥(affinoid ϖ n) | (w : K) ∉ Set.range (fun γ : G => pmoebius K₀ (ρ γ) a)} := by
        apply dense_setOf_not_mem ϖ hex n
        refine ((finite_orbit_mem_affinoid ϖ hex ρ hρ ha n).image (fun γ : G => pmoebius K₀ (ρ γ) a)).subset ?_
        rintro x ⟨hx, γ, rfl⟩
        exact ⟨γ, hx, rfl⟩
      have hEq : Set.EqOn g₁ g₂ {w : ↥(affinoid ϖ n) | (w : K) ∉ Set.range (fun γ : G => pmoebius K₀ (ρ γ) a)} := by
        intro w hw
        have hwo : ¬ ∃ γ : G, pmoebius K₀ (ρ γ) a =
            ((Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) w : ↥(upperHalfPlane K₀ K)) : K) :=
          fun ⟨γ, h⟩ => hw ⟨γ, h⟩
        rw [hg₁v, hg₂v]
        exact hautU β _ hwo
      have key := congrFun (Continuous.ext_on hD (continuous_of_mem_holOn K hg₁) (continuous_of_mem_holOn K hg₂) hEq)
        ⟨z, hn⟩
      rw [hg₁v, hg₂v] at key
      have hincl : (Set.inclusion (affinoid_subset_upperHalfPlane ϖ n) ⟨(z : K), hn⟩ : ↥(upperHalfPlane K₀ K)) = z :=
        Subtype.ext rfl
      rw [hincl] at key
      exact key
    · exact hautU β z hzo

end S_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_isUnit_coe_eq_thetaMer_apply_smul_eq_period_mul (solution)
