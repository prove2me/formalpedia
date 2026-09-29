-- Prove2me | solution 1 for CerednikDrinfeld.Omega.exists_isThetaPair_ordAt_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0e363ca6-181b-5c1c-a5cc-aa31939837a1

import Mathlib
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_mem_holOn_hasProd_evalAt
import Theorems.Thm_CerednikDrinfeld_Omega_exists_blaschke_denominators
import Theorems.Thm_CerednikDrinfeld_Omega_finite_setOf_pmoebius_mem_affinoid
import Theorems.Thm_CerednikDrinfeld_Omega_eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt
import Theorems.Thm_CerednikDrinfeld_Omega_isDomain_holRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card

set_option autoImplicit false

open scoped MatrixGroups Topology
open Filter CerednikDrinfeld.Omega

namespace DivThetaSol

section Generic

variable {K : Type} [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem v_eq_one_of_v_sub_one_lt {x : K} {ε : Γ₀} (hx : Valued.v (x - 1) < ε) (hε : ε ≤ 1) :
    Valued.v x = 1 := by
  have h : Valued.v (x - 1) < Valued.v (1 : K) := by rw [map_one]; exact lt_of_lt_of_le hx hε
  have := Valuation.map_add_eq_of_lt_left Valued.v h
  rwa [add_sub_cancel, map_one] at this

theorem v_mul_sub_one_lt {x y : K} {ε : Γ₀} (hx : Valued.v (x - 1) < ε) (hy : Valued.v (y - 1) < ε)
    (hε : ε ≤ 1) : Valued.v (x * y - 1) < ε := by
  have hx1 := v_eq_one_of_v_sub_one_lt hx hε
  have : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [this]
  refine Valuation.map_add_lt _ ?_ hx
  rw [Valuation.map_mul, hx1, one_mul]
  exact hy

theorem hasProd_inv₀ {ι : Type} {f : ι → K} {a : K} (h : HasProd f a) (ha : a ≠ 0) :
    HasProd (fun i => (f i)⁻¹) a⁻¹ := by
  show Tendsto (fun s : Finset ι => ∏ i ∈ s, (f i)⁻¹) atTop (𝓝 a⁻¹)
  simp_rw [Finset.prod_inv_distrib]
  exact (show Tendsto (fun s : Finset ι => ∏ i ∈ s, f i) atTop (𝓝 a) from h).inv₀ ha

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

omit [Algebra K₀ K] in
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

end Generic

section Family

variable {K : Type} [Field K] {ι : Type}

noncomputable def linFam (κ w : ι → K) (d : ι → Polynomial K) (γ : ι) : RatPair K :=
  ⟨Polynomial.C (κ γ) * (Polynomial.X - Polynomial.C (w γ)), d γ⟩

theorem linFam_evalAt (κ w : ι → K) (d : ι → Polynomial K) (γ : ι) (z : K) :
    (linFam κ w d γ).evalAt z = κ γ * (z - w γ) / (d γ).eval z := by
  simp [linFam, RatPair.evalAt]

theorem linFam_den (κ w : ι → K) (d : ι → Polynomial K) (γ : ι) : (linFam κ w d γ).den = d γ := rfl

end Family

section Omega

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem finite_orbit_mem_affinoid [DecidableEq K] {G : Type} [Group G] (ϖ : PseudoUniformizer K₀ K)
    (hex : IsExhausted ϖ) (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ) {a : K} (ha : a ∈ upperHalfPlane K₀ K)
    (n : ℕ) : {γ : G | pmoebius K₀ (ρ γ) a ∈ affinoid ϖ n}.Finite := by
  obtain ⟨m, hm⟩ := hex a ha
  have hsub : {γ : G | pmoebius K₀ (ρ γ) a ∈ affinoid ϖ n} ⊆
      {γ : G | pmoebius K₀ (ρ γ) a ∈ affinoid ϖ (max n m)} :=
    fun γ hγ => affinoid_mono ϖ (le_max_left n m) hγ
  exact (finite_setOf_pmoebius_mem_affinoid ϖ ρ hρ (max n m) (affinoid_mono ϖ (le_max_right n m) hm)).subset hsub

variable (ϖ : PseudoUniformizer K₀ K)

theorem add_one_mem_upperHalfPlane {z : K} (hz : z ∈ upperHalfPlane K₀ K) : z + 1 ∈ upperHalfPlane K₀ K := by
  rw [mem_upperHalfPlane_iff] at hz ⊢
  intro a ha
  exact hz (a - 1) (by rw [map_sub, map_one, ha, add_sub_cancel_right])

theorem coe_mul_apply (F G : ↥(holRing ϖ)) (w : ↥(upperHalfPlane K₀ K)) :
    ((F * G : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w =
      (F : ↥(upperHalfPlane K₀ K) → K) w * (G : ↥(upperHalfPlane K₀ K) → K) w := rfl

theorem coe_pow_apply (F : ↥(holRing ϖ)) (n : ℕ) (w : ↥(upperHalfPlane K₀ K)) :
    ((F ^ n : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w = ((F : ↥(upperHalfPlane K₀ K) → K) w) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, coe_mul_apply, ih, pow_succ]

theorem coe_prod_apply {ι : Type} (T : Finset ι) (g : ι → ↥(holRing ϖ)) (w : ↥(upperHalfPlane K₀ K)) :
    ((∏ γ ∈ T, g γ : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w =
      ∏ γ ∈ T, (g γ : ↥(upperHalfPlane K₀ K) → K) w :=
  map_prod ((Pi.evalRingHom (fun _ : ↥(upperHalfPlane K₀ K) => K) w).comp (holRing ϖ).subtype) g T

theorem coordSub_ne_zero (z : ↥(upperHalfPlane K₀ K)) : coordSub ϖ z ≠ 0 := by
  intro h
  have h1 := congrArg (fun F : ↥(holRing ϖ) => (F : ↥(upperHalfPlane K₀ K) → K)
    ⟨(z : K) + 1, add_one_mem_upperHalfPlane z.2⟩) h
  simp only [coordSub_apply, add_sub_cancel_left] at h1
  exact one_ne_zero h1

theorem ordAt_eq_of_eq_pow_mul [IsDomain ↥(holRing ϖ)] (F U : ↥(holRing ϖ)) (z : ↥(upperHalfPlane K₀ K)) (k : ℕ)
    (hF : F = coordSub ϖ z ^ k * U) (hU : (U : ↥(upperHalfPlane K₀ K) → K) z ≠ 0) :
    ordAt ϖ F z = k := by
  have hc : coordSub ϖ z ≠ 0 := coordSub_ne_zero ϖ z
  have hup : ∀ n : ℕ, coordSub ϖ z ^ n ∣ F → n ≤ k := by
    intro n hn
    by_contra hlt
    have hk : k + 1 ≤ n := by omega
    obtain ⟨G, hG⟩ := (pow_dvd_pow (coordSub ϖ z) hk).trans hn
    rw [hF, pow_succ, mul_assoc] at hG
    have hUG : U = coordSub ϖ z * G := mul_left_cancel₀ (pow_ne_zero k hc) hG
    apply hU
    rw [hUG, coe_mul_apply, coordSub_apply_self, zero_mul]
  exact le_antisymm (ordAt_le_of_forall_le ϖ F z k hup) (le_ordAt_of_pow_dvd ϖ F z ⟨U, hF⟩ ⟨k, fun n hn => hup n hn⟩)

end Omega

section Global

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
  (ϖ : PseudoUniformizer K₀ K)

theorem globalProd (hex : IsExhausted ϖ) {ι : Type} (r : ι → RatPair K)
    (hpf : ∀ γ, ∀ z ∈ upperHalfPlane K₀ K, (r γ).den.eval z ≠ 0)
    (hbd : ∀ (n : ℕ) (γ : ι), ∃ b : K, ∀ z ∈ affinoid ϖ n, Valued.v ((r γ).evalAt z) ≤ Valued.v b)
    (h1 : ∀ (n : ℕ) (c : K), c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((r γ).evalAt z - 1) < Valued.v c) :
    ∃ P : ↥(holRing ϖ),
      (∀ z : ↥(upperHalfPlane K₀ K),
        HasProd (fun γ => (r γ).evalAt (z : K)) ((P : ↥(upperHalfPlane K₀ K) → K) z)) ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (P : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ, (r γ).evalAt (z : K) = 0) := by
  have lev : ∀ n : ℕ, ∃ P : ↥(affinoid ϖ n) → K, P ∈ holOn K (affinoid ϖ n) ∧
      (∀ z : ↥(affinoid ϖ n), HasProd (fun γ => (r γ).evalAt (z : K)) (P z)) ∧
      (∀ z : ↥(affinoid ϖ n), P z = 0 ↔ ∃ γ, (r γ).evalAt (z : K) = 0) := fun n =>
    unifProd ϖ hex (S := affinoid ϖ n) r (fun γ z hz => hpf γ z (affinoid_subset_upperHalfPlane ϖ n hz))
      (hbd n) (h1 n)
  let P₀ : ↥(upperHalfPlane K₀ K) → K := fun z => ∏' γ, (r γ).evalAt (z : K)
  have hP₀ : P₀ ∈ holRing ϖ := by
    intro n
    obtain ⟨P, hP, hprod, -⟩ := lev n
    have : restrictAffinoid ϖ n P₀ = P := funext fun z => (hprod z).tprod_eq
    rw [this]
    exact hP
  refine ⟨⟨P₀, hP₀⟩, fun z => ?_, fun z => ?_⟩
  · obtain ⟨n, hn⟩ := hex (z : K) z.2
    obtain ⟨P, -, hprod, -⟩ := lev n
    exact (hprod ⟨z, hn⟩).multipliable.hasProd
  · obtain ⟨n, hn⟩ := hex (z : K) z.2
    obtain ⟨P, -, hprod, hzero⟩ := lev n
    show P₀ z = 0 ↔ _
    rw [show P₀ z = P ⟨z, hn⟩ from (hprod ⟨z, hn⟩).tprod_eq]
    exact hzero ⟨z, hn⟩

theorem linProd [IsDomain ↥(holRing ϖ)] (hex : IsExhausted ϖ) {ι : Type} (κ w : ι → K) (d : ι → Polynomial K)
    (hκ : ∀ γ, κ γ ≠ 0)
    (hwfin : ∀ n : ℕ, {γ | w γ ∈ affinoid ϖ n}.Finite)
    (hd2 : ∀ γ, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0)
    (hd3 : ∀ (n : ℕ) (γ : ι) (w' : K), ∃ b : K, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - w') / (d γ).eval z) ≤ Valued.v b)
    (h1 : ∀ (n : ℕ) (c : K), c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((linFam κ w d γ).evalAt z - 1) < Valued.v c) :
    ∃ P : ↥(holRing ϖ),
      (∀ z : ↥(upperHalfPlane K₀ K),
        HasProd (fun γ => (linFam κ w d γ).evalAt (z : K)) ((P : ↥(upperHalfPlane K₀ K) → K) z)) ∧
      (∀ z : ↥(upperHalfPlane K₀ K),
        (P : ↥(upperHalfPlane K₀ K) → K) z = 0 ↔ ∃ γ, w γ = (z : K)) ∧
      (∀ z : ↥(upperHalfPlane K₀ K), ordAt ϖ P z = Nat.card {γ : ι // w γ = (z : K)}) := by
  classical

  have hpf : ∀ γ, ∀ z ∈ upperHalfPlane K₀ K, ((linFam κ w d γ).den).eval z ≠ 0 := fun γ z hz => hd2 γ z hz
  have hbd : ∀ (n : ℕ) (γ : ι), ∃ b : K, ∀ z ∈ affinoid ϖ n,
      Valued.v ((linFam κ w d γ).evalAt z) ≤ Valued.v b := by
    intro n γ
    obtain ⟨b, hb⟩ := hd3 n γ (w γ)
    refine ⟨κ γ * b, fun z hz => ?_⟩
    rw [linFam_evalAt, mul_div_assoc, Valuation.map_mul, Valuation.map_mul]
    exact mul_le_mul_right (hb z hz) _

  have hfac0 : ∀ (γ : ι) (z : K), z ∈ upperHalfPlane K₀ K →
      ((linFam κ w d γ).evalAt z = 0 ↔ w γ = z) := by
    intro γ z hz
    rw [linFam_evalAt, div_eq_zero_iff, mul_eq_zero, sub_eq_zero]
    constructor
    · rintro ((h | h) | h)
      · exact absurd h (hκ γ)
      · exact h.symm
      · exact absurd h (hd2 γ z hz)
    · intro h
      exact Or.inl (Or.inr h.symm)

  have hinv_mem : ∀ γ, (fun w' : ↥(upperHalfPlane K₀ K) => ((d γ).eval (w' : K))⁻¹) ∈ holRing ϖ := by
    intro γ n
    obtain ⟨b, hb⟩ := exists_bound_inv (S := affinoid ϖ n) (d γ) (hd3 n γ 0) (hd3 n γ 1)
    have h := isHolOn_ratPair (S := affinoid ϖ n) (⟨1, d γ⟩ : RatPair K)
      (fun z hz => hd2 γ z (affinoid_subset_upperHalfPlane ϖ n hz))
      ⟨b, fun z hz => by simpa [RatPair.evalAt] using hb z hz⟩
    convert h using 1
    funext z
    simp [restrictAffinoid, RatPair.evalAt]
  let invD : ι → ↥(holRing ϖ) := fun γ => ⟨fun w' => ((d γ).eval (w' : K))⁻¹, hinv_mem γ⟩
  have invD_apply : ∀ (γ : ι) (w' : ↥(upperHalfPlane K₀ K)),
      (invD γ : ↥(upperHalfPlane K₀ K) → K) w' = ((d γ).eval (w' : K))⁻¹ := fun _ _ => rfl

  obtain ⟨P, hprod, hzero⟩ := globalProd ϖ hex (linFam κ w d) hpf hbd h1
  refine ⟨P, hprod, fun z => (hzero z).trans (exists_congr fun γ => hfac0 γ z z.2), fun z => ?_⟩

  obtain ⟨n, hn⟩ := hex (z : K) z.2
  set S : Set ι := {γ | w γ = (z : K)} with hS_def
  have hS : S.Finite := (hwfin n).subset fun γ (hγ : w γ = (z : K)) => by
    show w γ ∈ affinoid ϖ n
    rw [hγ]; exact hn
  set T : Finset ι := hS.toFinset with hT_def
  have hmemT : ∀ γ, γ ∈ T ↔ w γ = (z : K) := fun γ => by rw [hT_def, Set.Finite.mem_toFinset]; rfl

  have hinj : Function.Injective (Subtype.val : ↥((↑T : Set ι)ᶜ) → ι) := Subtype.val_injective
  obtain ⟨Q, hQprod, hQzero⟩ := globalProd ϖ hex (fun γ : ↥((↑T : Set ι)ᶜ) => linFam κ w d γ.1)
    (fun γ => hpf γ.1) (fun n γ => hbd n γ.1) (fun n c hc => (hinj.tendsto_cofinite).eventually (h1 n c hc))
  have hQz : (Q : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := by
    intro h0
    obtain ⟨γ, hγ⟩ := (hQzero z).1 h0
    have hγT : γ.1 ∈ T := (hmemT γ.1).2 ((hfac0 γ.1 z z.2).1 hγ)
    exact γ.2 hγT

  set U : ↥(holRing ϖ) := (∏ γ ∈ T, (algebraMap K ↥(holRing ϖ) (κ γ) * invD γ)) * Q with hU_def
  have hUz : (U : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := by
    rw [hU_def, coe_mul_apply, coe_prod_apply]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun γ _ => ?_) hQz
    rw [coe_mul_apply, algebraMap_holRing_apply, invD_apply]
    exact mul_ne_zero (hκ γ) (inv_ne_zero (hd2 γ _ z.2))

  have hPw : ∀ w' : ↥(upperHalfPlane K₀ K), (P : ↥(upperHalfPlane K₀ K) → K) w' =
      (∏ γ ∈ T, (linFam κ w d γ).evalAt (w' : K)) * (Q : ↥(upperHalfPlane K₀ K) → K) w' := by
    intro w'
    have h := (T.hasProd (fun γ => (linFam κ w d γ).evalAt (w' : K))).mul_compl (hQprod w')
    exact (hprod w').unique h
  have hPfac : P = coordSub ϖ z ^ T.card * U := by
    apply Subtype.ext
    funext w'
    rw [hPw w', coe_mul_apply, coe_pow_apply, coordSub_apply, hU_def, coe_mul_apply, coe_prod_apply, ← mul_assoc]
    congr 1
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun γ hγ => ?_
    rw [coe_mul_apply, algebraMap_holRing_apply, invD_apply, linFam_evalAt, (hmemT γ).1 hγ]
    rw [div_eq_mul_inv]
    ring
  rw [ordAt_eq_of_eq_pow_mul ϖ P U z T.card hPfac hUz]
  exact (Nat.subtype_card T hmemT).symm

variable [DecidableEq K] {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

omit [CompleteSpace K] in
theorem est_F (hex : IsExhausted ϖ) (hρ : IsDiscrete K ρ) {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K)
    (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (d : G → Polynomial K)
    (hd2 : ∀ γ : G, ∀ z ∈ upperHalfPlane K₀ K, (d γ).eval z ≠ 0)
    (hd4 : ∀ (n : ℕ) (c : K), c ≠ 0 → ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((z - pmoebius K₀ (ρ γ) b) / (d γ).eval z - 1) < Valued.v c)
    (n : ℕ) (c : K) (hc : c ≠ 0) (hc1 : Valued.v c ≤ 1) :
    ∀ᶠ γ in cofinite, ∀ z ∈ affinoid ϖ n,
      Valued.v ((linFam (fun γ : G => (z₀ - pmoebius K₀ (ρ γ) b) / (z₀ - pmoebius K₀ (ρ γ) a))
        (fun γ : G => pmoebius K₀ (ρ γ) a) d γ).evalAt z - 1) < Valued.v c := by
  obtain ⟨na, hna⟩ := hex a ha
  obtain ⟨nb, hnb⟩ := hex b hb
  obtain ⟨nz, hnz⟩ := hex z₀ hz₀
  have hnN : n ≤ max (max n na) (max nb nz) := (le_max_left _ _).trans (le_max_left _ _)
  have haN : a ∈ affinoid ϖ (max (max n na) (max nb nz)) :=
    affinoid_mono ϖ ((le_max_right _ _).trans (le_max_left _ _)) hna
  have hbN : b ∈ affinoid ϖ (max (max n na) (max nb nz)) :=
    affinoid_mono ϖ ((le_max_left _ _).trans (le_max_right _ _)) hnb
  have hzN : z₀ ∈ affinoid ϖ (max (max n na) (max nb nz)) :=
    affinoid_mono ϖ ((le_max_right _ _).trans (le_max_right _ _)) hnz
  have hε : Valued.v c ≠ 0 := fun h => hc ((Valuation.zero_iff _).1 h)
  have hT := eventually_cofinite_forall_mem_affinoid_v_thetaFactor_sub_one_lt ϖ ρ hρ _ haN hbN hzN
    (Valued.v c) hε
  have hA := hd4 n c hc
  have hFb : ∀ᶠ γ in cofinite, pmoebius K₀ (ρ γ) b ∉ affinoid ϖ n := by
    rw [Filter.eventually_cofinite]
    simp only [not_not]
    exact finite_orbit_mem_affinoid ϖ hex ρ hρ hb n
  filter_upwards [hT, hA, hFb] with γ h1 h2 h3
  intro z hz
  have hzΩ : z ∈ upperHalfPlane K₀ K := affinoid_subset_upperHalfPlane ϖ n hz
  have hx1 := h1 z (affinoid_mono ϖ hnN hz)
  have hx2 := h2 z hz
  have hzb : z - pmoebius K₀ (ρ γ) b ≠ 0 := sub_ne_zero.2 fun h => h3 (h ▸ hz)
  have hdγ : (d γ).eval z ≠ 0 := hd2 γ z hzΩ
  have h0a : z₀ - pmoebius K₀ (ρ γ) a ≠ 0 := sub_ne_zero.2 fun h => hz₀a γ h.symm
  have hid : (linFam (fun γ : G => (z₀ - pmoebius K₀ (ρ γ) b) / (z₀ - pmoebius K₀ (ρ γ) a))
      (fun γ : G => pmoebius K₀ (ρ γ) a) d γ).evalAt z =
      thetaFactor ρ a b z₀ z γ * ((z - pmoebius K₀ (ρ γ) b) / (d γ).eval z) := by
    rw [linFam_evalAt, thetaFactor, crossRatio]
    field_simp
  rw [hid]
  exact v_mul_sub_one_lt hx1 hx2 hc1

end Global

end DivThetaSol

open DivThetaSol in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K] [IsAlgClosed K]
    (ϖ : PseudoUniformizer K₀ K)
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
    (hex : IsExhausted ϖ)
    (hfin : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    ∃ F H : ↥(holRing ϖ), IsThetaPair ϖ ρ a b z₀ F H ∧
      ∀ z : ↥(upperHalfPlane K₀ K),
        ordAt ϖ F z = Nat.card {γ : G // pmoebius K₀ (ρ γ) a = (z : K)} ∧
        ordAt ϖ H z = Nat.card {γ : G // pmoebius K₀ (ρ γ) b = (z : K)} := by
  haveI : IsDomain ↥(holRing ϖ) := isDomain_holRing K₀ K ϖ hrk hex hfin

  have hwa : ∀ γ : G, pmoebius K₀ (ρ γ) a ∈ upperHalfPlane K₀ K := fun γ => pmoebius_mem_upperHalfPlane K₀ ha (ρ γ)
  have hwb : ∀ γ : G, pmoebius K₀ (ρ γ) b ∈ upperHalfPlane K₀ K := fun γ => pmoebius_mem_upperHalfPlane K₀ hb (ρ γ)
  have hfa : ∀ n : ℕ, {γ : G | pmoebius K₀ (ρ γ) a ∈ affinoid ϖ n}.Finite := finite_orbit_mem_affinoid ϖ hex ρ hρ ha
  have hfb : ∀ n : ℕ, {γ : G | pmoebius K₀ (ρ γ) b ∈ affinoid ϖ n}.Finite := finite_orbit_mem_affinoid ϖ hex ρ hρ hb

  obtain ⟨d, -, hd2, hd3, hd4⟩ :=
    exists_blaschke_denominators K₀ K ϖ hex (fun γ : G => pmoebius K₀ (ρ γ) b) hwb hfb

  have hκ : ∀ γ : G, (z₀ - pmoebius K₀ (ρ γ) b) / (z₀ - pmoebius K₀ (ρ γ) a) ≠ 0 := fun γ =>
    div_ne_zero (sub_ne_zero.2 fun h => hz₀b γ h.symm) (sub_ne_zero.2 fun h => hz₀a γ h.symm)

  obtain ⟨H, hHprod, hHzero, hHord⟩ := linProd ϖ hex (fun _ : G => (1 : K)) (fun γ : G => pmoebius K₀ (ρ γ) b) d
    (fun _ => one_ne_zero) hfb hd2 hd3
    (fun n c hc => by
      filter_upwards [hd4 n c hc] with γ hγ z hz
      rw [linFam_evalAt, one_mul]
      exact hγ z hz)

  obtain ⟨F, hFprod, hFzero, hFord⟩ := linProd ϖ hex
    (fun γ : G => (z₀ - pmoebius K₀ (ρ γ) b) / (z₀ - pmoebius K₀ (ρ γ) a)) (fun γ : G => pmoebius K₀ (ρ γ) a) d
    hκ hfa hd2 hd3
    (fun n c hc => by
      by_cases hc1 : Valued.v c ≤ 1
      · exact est_F ϖ ρ hex hρ ha hb hz₀ hz₀a d hd2 hd4 n c hc hc1
      · have h := est_F ϖ ρ hex hρ ha hb hz₀ hz₀a d hd2 hd4 n 1 one_ne_zero (le_of_eq (map_one _))
        filter_upwards [h] with γ hγ z hz
        exact (hγ z hz).trans (by rw [map_one]; exact lt_of_not_ge hc1))
  refine ⟨F, H, ⟨?_, hHzero, hFzero, ?_⟩, fun z => ⟨hFord z, hHord z⟩⟩
  ·
    apply mem_nonZeroDivisors_of_ne_zero
    intro hH0
    have h0 : (H : ↥(upperHalfPlane K₀ K) → K) ⟨z₀, hz₀⟩ = 0 := by rw [hH0]; rfl
    obtain ⟨γ, hγ⟩ := (hHzero ⟨z₀, hz₀⟩).1 h0
    exact hz₀b γ hγ
  ·
    intro z hzo
    have hH0 : (H : ↥(upperHalfPlane K₀ K) → K) z ≠ 0 := fun h => hzo ((hHzero z).1 h)
    have hq := (hFprod z).mul (hasProd_inv₀ (hHprod z) hH0)
    have hfun : (fun γ : G => (linFam (fun γ : G => (z₀ - pmoebius K₀ (ρ γ) b) / (z₀ - pmoebius K₀ (ρ γ) a))
        (fun γ : G => pmoebius K₀ (ρ γ) a) d γ).evalAt (z : K) *
        ((linFam (fun _ : G => (1 : K)) (fun γ : G => pmoebius K₀ (ρ γ) b) d γ).evalAt (z : K))⁻¹) =
        fun γ : G => thetaFactor ρ a b z₀ (z : K) γ := by
      funext γ
      have hzb : (z : K) - pmoebius K₀ (ρ γ) b ≠ 0 := sub_ne_zero.2 fun h => hzo ⟨γ, h.symm⟩
      have hdγ : (d γ).eval (z : K) ≠ 0 := hd2 γ _ z.2
      have h0a : z₀ - pmoebius K₀ (ρ γ) a ≠ 0 := sub_ne_zero.2 fun h => hz₀a γ h.symm
      rw [linFam_evalAt, linFam_evalAt, one_mul, thetaFactor, crossRatio]
      field_simp
    rw [hfun] at hq
    rw [div_eq_mul_inv]
    exact hq.tprod_eq.symm

end S_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_exists_isThetaPair_ordAt_eq_card (solution)
