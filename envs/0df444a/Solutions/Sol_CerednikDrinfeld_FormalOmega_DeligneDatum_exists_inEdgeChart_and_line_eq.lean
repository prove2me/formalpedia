-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_inEdgeChart_and_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a1158de7-a072-5b57-b3b9-94589401cb80

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcOmegaExt

section Generation

variable {R : Type} [CommRing R] {Q : Type} [AddCommGroup Q] [Module R Q]

theorem eq_top_of_mem_of_forall_not_mem_smul_top [Module.Invertible R Q] (N : Submodule R Q) (q : Q)
    (hqN : q ∈ N) (hq : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → q ∉ (𝔪 • ⊤ : Submodule R Q)) : N = ⊤ := by
  set A : Ideal R := N.colon (Set.univ : Set Q) with hA_def
  by_cases hA : A = ⊤
  · have h1 : (1 : R) ∈ A := by rw [hA]; exact Submodule.mem_top
    rw [hA_def, Submodule.mem_colon] at h1
    refine eq_top_iff.mpr fun m _ => ?_
    have := h1 m (Set.mem_univ m)
    rwa [one_smul] at this
  · exfalso
    obtain ⟨𝔪, h𝔪, hA𝔪⟩ := Ideal.exists_le_maximal A hA
    obtain ⟨φ, hφ⟩ := exists_linearMap_apply_not_mem 𝔪 q (hq 𝔪 h𝔪)
    obtain ⟨c, hc⟩ := (Module.Invertible.toModuleEnd_bijective R Q).2 (LinearMap.smulRight φ q)
    have hc' : ∀ x : Q, c • x = φ x • q := fun x => by
      have := congrArg (fun f : Module.End R Q => f x) hc
      simp only [LinearMap.smulRight_apply] at this
      exact this
    have hcA : c ∈ A := by
      rw [hA_def, Submodule.mem_colon]
      intro m _
      rw [hc' m]
      exact N.smul_mem _ hqN
    have hkey : (φ q - c) * φ q = 0 := by
      have h := congrArg φ (hc' q)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
      rw [sub_mul, ← h, sub_self]
    have hmem : (φ q - c) * φ q ∈ 𝔪 := by rw [hkey]; exact 𝔪.zero_mem
    rcases h𝔪.isPrime.mem_or_mem hmem with h1 | h1
    · apply hφ
      have : φ q = (φ q - c) + c := by ring
      rw [this]
      exact 𝔪.add_mem h1 (hA𝔪 hcA)
    · exact hφ h1

theorem mem_sup_smul_top_of_mkQ_mem {V : Type} [AddCommGroup V] [Module R V] (N : Submodule R V) (I : Ideal R)
    (x : V) (hx : N.mkQ x ∈ (I • ⊤ : Submodule R (V ⧸ N))) : x ∈ N ⊔ (I • ⊤ : Submodule R V) := by
  have : x ∈ ((I • ⊤ : Submodule R V).map N.mkQ).comap N.mkQ := by
    rw [Submodule.mem_comap, Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]; exact hx
  rwa [Submodule.comap_map_mkQ] at this

variable {V W : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

theorem surjective_mkQ_comp_of_generator (N : Submodule R W) [Module.Invertible R (W ⧸ N)] (f : V →ₗ[R] W) (v : V)
    (hv : ∀ 𝔪 : Ideal R, 𝔪.IsMaximal → f v ∉ N ⊔ (𝔪 • ⊤ : Submodule R W)) :
    Function.Surjective (N.mkQ ∘ₗ f) := by
  rw [← LinearMap.range_eq_top]
  apply eq_top_of_mem_of_forall_not_mem_smul_top _ (N.mkQ (f v)) (LinearMap.mem_range.mpr ⟨v, rfl⟩)
  intro 𝔪 h𝔪 hmem
  exact hv 𝔪 h𝔪 (mem_sup_smul_top_of_mkQ_mem _ _ _ hmem)

theorem comap_eq_ker_mkQ_comp (N : Submodule R W) (f : V →ₗ[R] W) : N.comap f = LinearMap.ker (N.mkQ ∘ₗ f) := by
  rw [LinearMap.ker_comp, Submodule.ker_mkQ]

def quotComapEquiv (N : Submodule R W) (f : V →ₗ[R] W) (hf : Function.Surjective (N.mkQ ∘ₗ f)) :
    (V ⧸ N.comap f) ≃ₗ[R] (W ⧸ N) :=
  (Submodule.quotEquivOfEq _ _ (comap_eq_ker_mkQ_comp N f)).trans (LinearMap.quotKerEquivOfSurjective _ hf)

theorem invertible_quot_comap (N : Submodule R W) [Module.Invertible R (W ⧸ N)] (f : V →ₗ[R] W)
    (hf : Function.Surjective (N.mkQ ∘ₗ f)) : Module.Invertible R (V ⧸ N.comap f) :=
  Module.Invertible.congr (quotComapEquiv N f hf).symm

theorem eq_of_le_of_invertible (N₁ N₂ : Submodule R V) [Module.Invertible R (V ⧸ N₁)] [Module.Invertible R (V ⧸ N₂)]
    (hle : N₁ ≤ N₂) : N₁ = N₂ := by
  apply le_antisymm hle
  have hle' : N₁ ≤ N₂.comap (LinearMap.id : V →ₗ[R] V) := by rw [Submodule.comap_id]; exact hle
  let f : (V ⧸ N₁) →ₗ[R] (V ⧸ N₂) := Submodule.mapQ _ _ LinearMap.id hle'
  have hf : ∀ x, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => Submodule.mapQ_apply _ _ _ x
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, hf x⟩
  have hinj := (Module.Invertible.bijective_of_surjective hsurj).1
  intro x hx
  have h0 : f (Submodule.Quotient.mk x) = 0 := by
    rw [hf]; exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have h1 : (Submodule.Quotient.mk x : V ⧸ N₁) = 0 := hinj (by rw [h0, map_zero])
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

theorem smul_mem_iff_of_isUnit (N : Submodule R V) {r : R} (hr : IsUnit r) (x : V) : r • x ∈ N ↔ x ∈ N := by
  refine ⟨fun h => ?_, fun h => N.smul_mem r h⟩
  obtain ⟨u, rfl⟩ := hr
  have : x = (↑u⁻¹ : R) • ((u : R) • x) := by rw [smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact N.smul_mem _ h

end Generation

section Scaling

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
variable {ϖ : R}

theorem alg_ne_zero {x : R} (hx : x ≠ 0) : algebraMap R K x ≠ 0 :=
  fun h => hx (IsFractionRing.injective R K (by rw [h, map_zero]))

theorem sc_le_iff (c : Kˣ) (L L' : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) L ≤ L' ↔ ∀ w ∈ L, (c : K) • w ∈ L' := by
  constructor
  · intro h w hw
    exact h (mem_latticeMap_scalarGL.mpr ⟨w, hw, rfl⟩)
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := mem_latticeMap_scalarGL.mp hv
    exact h w hw

theorem algebraMap_smul_mem (L : Submodule R (Fin 2 → K)) (r : R) {w : Fin 2 → K} (hw : w ∈ L) :
    algebraMap R K r • w ∈ L := by
  rw [algebraMap_smul]
  exact L.smul_mem r hw

def piU (hϖ : Irreducible ϖ) : Kˣ := unitOfNeZero (K := K) hϖ.ne_zero

theorem piU_coe (hϖ : Irreducible ϖ) : ((piU (K := K) hϖ : Kˣ) : K) = algebraMap R K ϖ := rfl

theorem piU_pow_coe (hϖ : Irreducible ϖ) (n : ℕ) :
    ((piU (K := K) hϖ ^ n : Kˣ) : K) = algebraMap R K (ϖ ^ n) := by
  rw [Units.val_pow_eq_pow_val, piU_coe, map_pow]

theorem pow_smul_mem (hϖ : Irreducible ϖ) (L : Submodule R (Fin 2 → K)) (n : ℕ) {w : Fin 2 → K}
    (hw : w ∈ L) : ((piU (K := K) hϖ ^ n : Kˣ) : K) • w ∈ L := by
  rw [piU_pow_coe]
  exact algebraMap_smul_mem L _ hw

theorem sc_sc (c d : Kˣ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL c) (latticeMap (scalarGL d) L) = latticeMap (scalarGL (c * d)) L := by
  rw [scalarGL_mul, latticeMap_mul]

theorem exists_pow_smul_mem (hϖ : Irreducible ϖ) {L : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (v : Fin 2 → K) :
    ∃ n : ℕ, ((piU (K := K) hϖ ^ n : Kˣ) : K) • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set (Fin 2 → K)) := by
    rw [hL.2]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by rwa [pow_zero, Units.val_one, one_smul]⟩
  | zero => exact ⟨0, by rw [smul_zero]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
      obtain ⟨m, hm⟩ := hx
      obtain ⟨n, hn⟩ := hy
      refine ⟨m + n, ?_⟩
      rw [smul_add]
      refine L.add_mem ?_ ?_
      · rw [add_comm, pow_add, Units.val_mul, mul_smul]
        exact pow_smul_mem hϖ L n hm
      · rw [pow_add, Units.val_mul, mul_smul]
        exact pow_smul_mem hϖ L m hn
  | smul c x _ hx =>
      obtain ⟨n, hn⟩ := hx
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) c
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨e, u, hbu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
      refine ⟨e + n, ?_⟩
      have hπ : algebraMap R K ϖ ≠ 0 := alg_ne_zero hϖ.ne_zero
      have hu : algebraMap R K u ≠ 0 := alg_ne_zero u.ne_zero
      have key : ((piU (K := K) hϖ ^ (e + n) : Kˣ) : K) * (algebraMap R K a / algebraMap R K b) =
          algebraMap R K (a * ↑u⁻¹) * ((piU (K := K) hϖ ^ n : Kˣ) : K) := by
        rw [hbu, piU_pow_coe, piU_pow_coe, map_mul, map_mul, map_pow, map_pow, map_pow,
          map_units_inv, pow_add]
        field_simp
      rw [smul_smul, key, mul_smul, algebraMap_smul]
      exact L.smul_mem _ hn

theorem exists_sc_pow_le (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hM : IsFullLattice M) :
    ∃ n : ℕ, latticeMap (scalarGL (piU (K := K) hϖ ^ n)) M ≤ L := by
  obtain ⟨s, hs⟩ := hM.1
  choose f hf using fun v : Fin 2 → K => exists_pow_smul_mem hϖ hL v
  refine ⟨s.sup f, (sc_le_iff _ _ _).2 ?_⟩
  rw [← hs]
  intro w hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
      have hle : f x ≤ s.sup f := Finset.le_sup (Finset.mem_coe.mp hx)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      rw [hk, add_comm, pow_add, Units.val_mul, mul_smul]
      exact pow_smul_mem hϖ L k (hf x)
  | zero =>
      rw [smul_zero]
      exact L.zero_mem
  | add x y _ _ hx hy =>
      rw [smul_add]
      exact L.add_mem hx hy
  | smul r x _ hx =>
      rw [smul_comm]
      exact L.smul_mem r hx

theorem eq_zero_of_forall_pow_dvd (hϖ : Irreducible ϖ) {r : R} (h : ∀ n : ℕ, ϖ ^ n ∣ r) : r = 0 := by
  by_contra hr
  obtain ⟨m, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  obtain ⟨s, hs⟩ := h (m + 1)
  have h1 : (w : R) * ϖ ^ m = (ϖ * s) * ϖ ^ m := by
    rw [← hw, hs]; ring
  have h2 : (w : R) = ϖ * s := mul_right_cancel₀ (pow_ne_zero m hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ w.isUnit))

theorem exists_not_mem_sc_pow (hϖ : Irreducible ϖ) {M : Submodule R (Fin 2 → K)} (hM : IsFullLattice M)
    {v : Fin 2 → K} (hv : v ≠ 0) : ∃ n : ℕ, v ∉ latticeMap (scalarGL (piU (K := K) hϖ ^ n)) M := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_sc_pow_le hϖ (isFullLattice_stdLattice (R := R) (K := K)) hM
  apply hv
  have hcoord : ∀ (n : ℕ) (i : Fin 2), ∃ r : R, algebraMap R K (ϖ ^ n * r) =
      (((piU (K := K) hϖ ^ a : Kˣ) : K) • v) i := by
    intro n i
    obtain ⟨w, hw, hwv⟩ := mem_latticeMap_scalarGL.mp (hcon n)
    have hw' : ((piU (K := K) hϖ ^ a : Kˣ) : K) • w ∈ stdLattice R K :=
      ha (mem_latticeMap_scalarGL.mpr ⟨w, hw, rfl⟩)
    obtain ⟨r, hr⟩ : IsLocalization.IsInteger R ((((piU (K := K) hϖ ^ a : Kˣ) : K) • w) i) := hw' i
    refine ⟨r, ?_⟩
    rw [map_mul, ← piU_pow_coe hϖ, hr, ← hwv]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hzero : ((piU (K := K) hϖ ^ a : Kˣ) : K) • v = 0 := by
    funext i
    obtain ⟨r₀, hr₀⟩ := hcoord 0 i
    rw [pow_zero, one_mul] at hr₀
    have hr : r₀ = 0 := by
      apply eq_zero_of_forall_pow_dvd hϖ
      intro n
      obtain ⟨r, hr⟩ := hcoord n i
      rw [← hr₀] at hr
      exact ⟨r, (IsFractionRing.injective R K hr).symm⟩
    rw [Pi.zero_apply, ← hr₀, hr, map_zero]
  have hu : ((piU (K := K) hϖ ^ a : Kˣ) : K) ≠ 0 := Units.ne_zero _
  exact (smul_eq_zero.mp hzero).resolve_left hu

theorem exists_ne_zero_mem {L : Submodule R (Fin 2 → K)} (hL' : IsFullLattice L) : ∃ v ∈ L, v ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hbot : L = ⊥ := by
    rw [eq_bot_iff]; intro v hv; rw [Submodule.mem_bot]; exact hcon v hv
  have htop := hL'.2
  rw [hbot] at htop
  have hbt : (⊤ : Submodule K (Fin 2 → K)) = ⊥ := by
    rw [← htop, Submodule.span_eq_bot]
    intro x hx
    rw [SetLike.mem_coe, Submodule.mem_bot] at hx
    exact hx
  exact top_ne_bot hbt

theorem latticeMap_scalarGL_map_units (u : Rˣ) (L : Submodule R (Fin 2 → K)) :
    latticeMap (scalarGL (Units.map (algebraMap R K : R →* K) u)) L = L := by
  have key : ∀ (w : Rˣ) (v : Fin 2 → K), v ∈ L →
      ((Units.map (algebraMap R K : R →* K) w : Kˣ) : K) • v ∈ L := by
    intro w v hv
    rw [Units.coe_map, MonoidHom.coe_coe]
    exact algebraMap_smul_mem L _ hv
  apply le_antisymm
  · exact (sc_le_iff _ _ _).2 (key u)
  · intro v hv
    rw [mem_latticeMap_scalarGL]
    refine ⟨((Units.map (algebraMap R K : R →* K) u⁻¹ : Kˣ) : K) • v, key u⁻¹ v hv, ?_⟩
    rw [smul_smul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, one_smul]

theorem unit_zpow_decomp (hϖ : Irreducible ϖ) (c : Kˣ) :
    ∃ (u : Rˣ) (j : ℤ), c = Units.map (algebraMap R K : R →* K) u * (piU (K := K) hϖ) ^ j := by
  have hπK : algebraMap R K ϖ ≠ 0 := alg_ne_zero hϖ.ne_zero
  obtain ⟨a, b, hb, hc⟩ := IsFractionRing.div_surjective (A := R) (c : K)
  have hbz : (b : R) ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 := alg_ne_zero hbz
  have haz : a ≠ 0 := by
    intro ha
    apply c.ne_zero
    rw [← hc, ha, map_zero, zero_div]
  obtain ⟨m, u₁, hu₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible haz hϖ
  obtain ⟨n, u₂, hu₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hbz hϖ
  refine ⟨u₁ * u₂⁻¹, (m : ℤ) - (n : ℤ), Units.ext ?_⟩
  rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, Units.val_zpow_eq_zpow_val, piU_coe, ← hc, hu₁, hu₂,
    zpow_sub₀ hπK, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow, map_pow, Units.val_mul, map_mul,
    map_units_inv]
  have hu₂K : algebraMap R K (u₂ : R) ≠ 0 := alg_ne_zero u₂.ne_zero
  field_simp

def vchain (hϖ : Irreducible ϖ) (M : Submodule R (Fin 2 → K)) (n : ℤ) : Submodule R (Fin 2 → K) :=
  latticeMap (scalarGL (piU (K := K) hϖ ^ n)) M

theorem vchain_zero (hϖ : Irreducible ϖ) (M : Submodule R (Fin 2 → K)) : vchain hϖ M 0 = M := by
  rw [vchain, zpow_zero, scalarGL_one, latticeMap_one]

theorem vchain_add (hϖ : Irreducible ϖ) (M : Submodule R (Fin 2 → K)) (m n : ℤ) :
    vchain hϖ M (m + n) = latticeMap (scalarGL (piU (K := K) hϖ ^ m)) (vchain hϖ M n) := by
  rw [vchain, vchain, sc_sc, zpow_add]

theorem vchain_natCast_le (hϖ : Irreducible ϖ) (M : Submodule R (Fin 2 → K)) (k : ℕ) : vchain hϖ M k ≤ M := by
  rw [vchain, zpow_natCast]
  exact (sc_le_iff _ _ _).2 fun w hw => pow_smul_mem hϖ M k hw

theorem vchain_antitone (hϖ : Irreducible ϖ) (M : Submodule R (Fin 2 → K)) {n m : ℤ} (h : n ≤ m) :
    vchain hϖ M m ≤ vchain hϖ M n := by
  obtain ⟨k, hk⟩ := Int.le.dest h
  rw [← hk, add_comm, vchain_add, zpow_natCast]
  exact (sc_le_iff _ _ _).2 fun w hw => pow_smul_mem hϖ _ k hw

theorem latticeMap_units_vchain (hϖ : Irreducible ϖ) (M : Submodule R (Fin 2 → K)) (u : Rˣ) (n : ℤ) :
    latticeMap (scalarGL (Units.map (algebraMap R K : R →* K) u)) (vchain hϖ M n) = vchain hϖ M n :=
  latticeMap_scalarGL_map_units u _

theorem exists_le_vchain (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hM : IsFullLattice M) : ∃ n : ℤ, L ≤ vchain hϖ M n := by
  obtain ⟨a, ha⟩ := exists_sc_pow_le hϖ hM hL
  refine ⟨-(a : ℤ), ?_⟩
  have h1 := latticeMap_mono (R := R) (scalarGL (piU (K := K) hϖ ^ a)⁻¹) ha
  rw [sc_sc, inv_mul_cancel, scalarGL_one, latticeMap_one] at h1
  rw [vchain, zpow_neg, zpow_natCast]
  exact h1

theorem vchain_index_bdd (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hM : IsFullLattice M) : ∃ b : ℤ, ∀ n : ℤ, L ≤ vchain hϖ M n → n ≤ b := by
  obtain ⟨v, hvL, hv0⟩ := exists_ne_zero_mem hL
  obtain ⟨b, hb⟩ := exists_not_mem_sc_pow hϖ hM hv0
  refine ⟨b, fun n hn => ?_⟩
  by_contra hlt
  push Not at hlt
  apply hb
  have h1 : vchain hϖ M n ≤ vchain hϖ M b := vchain_antitone hϖ M hlt.le
  have h2 := h1 (hn hvL)
  rwa [vchain, zpow_natCast] at h2

theorem exists_level (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (hM : IsFullLattice M) : ∃ j : ℤ, L ≤ vchain hϖ M j ∧ ¬ L ≤ vchain hϖ M (j + 1) := by
  obtain ⟨b, hb⟩ := vchain_index_bdd hϖ hL hM
  obtain ⟨n₀, hn₀⟩ := exists_le_vchain hϖ hL hM
  obtain ⟨j, hj, hmax⟩ := Int.exists_greatest_of_bdd (P := fun n => L ≤ vchain hϖ M n) ⟨b, hb⟩ ⟨n₀, hn₀⟩
  exact ⟨j, hj, fun h => by have := hmax _ h; omega⟩

theorem level_unique (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)} {j j' : ℤ}
    (hj : L ≤ vchain hϖ M j ∧ ¬ L ≤ vchain hϖ M (j + 1)) (hj' : L ≤ vchain hϖ M j' ∧ ¬ L ≤ vchain hϖ M (j' + 1)) :
    j = j' := by
  rcases lt_trichotomy j j' with h | h | h
  · exact absurd (hj'.1.trans (vchain_antitone hϖ M (show j + 1 ≤ j' by omega))) hj.2
  · exact h
  · exact absurd (hj.1.trans (vchain_antitone hϖ M (show j' + 1 ≤ j by omega))) hj'.2

def lev (hϖ : Irreducible ϖ) (L M : FullLattice R K) : ℤ := (exists_level (K := K) hϖ L.2 M.2).choose

theorem lev_spec (hϖ : Irreducible ϖ) (L M : FullLattice R K) :
    L.1 ≤ vchain hϖ M.1 (lev hϖ L M) ∧ ¬ L.1 ≤ vchain hϖ M.1 (lev hϖ L M + 1) :=
  (exists_level (K := K) hϖ L.2 M.2).choose_spec

theorem lev_eq_of (hϖ : Irreducible ϖ) (L M : FullLattice R K) {j : ℤ}
    (h : L.1 ≤ vchain hϖ M.1 j ∧ ¬ L.1 ≤ vchain hϖ M.1 (j + 1)) : lev hϖ L M = j :=
  level_unique hϖ (lev_spec hϖ L M) h

theorem lev_le_lev_of_le (hϖ : Irreducible ϖ) {L' L : FullLattice R K} (M : FullLattice R K) (h : L'.1 ≤ L.1) :
    lev hϖ L M ≤ lev hϖ L' M := by
  by_contra hlt
  push Not at hlt
  have h1 : L'.1 ≤ vchain hϖ M.1 (lev hϖ L M) := h.trans (lev_spec hϖ L M).1
  exact (lev_spec hϖ L' M).2 (h1.trans (vchain_antitone hϖ M.1 (show lev hϖ L' M + 1 ≤ lev hϖ L M by omega)))

theorem not_le_sc_pi (hϖ : Irreducible ϖ) (M : FullLattice R K) :
    ¬ M.1 ≤ latticeMap (scalarGL (piU (K := K) hϖ)) M.1 := by
  intro h
  have h' : M.1 ≤ latticeMap (scalarGL (piU (K := K) hϖ ^ (1 : ℤ))) M.1 := by rwa [zpow_one]
  have hall : ∀ n : ℕ, M.1 ≤ vchain hϖ M.1 n := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero, vchain_zero]
    | succ n ih =>
        have h1 := latticeMap_mono (R := R) (scalarGL (piU (K := K) hϖ ^ (1 : ℤ))) ih
        rw [← vchain_add] at h1
        rw [Nat.cast_succ, add_comm]
        exact h'.trans h1
  obtain ⟨v, hvM, hv0⟩ := exists_ne_zero_mem M.2
  obtain ⟨b, hb⟩ := exists_not_mem_sc_pow hϖ M.2 hv0
  apply hb
  have := hall b hvM
  rwa [vchain, zpow_natCast] at this

theorem lev_self (hϖ : Irreducible ϖ) (M : FullLattice R K) : lev hϖ M M = 0 := by
  apply lev_eq_of
  refine ⟨by rw [vchain_zero], fun h => ?_⟩
  rw [zero_add, vchain, zpow_one] at h
  exact not_le_sc_pi hϖ M h

theorem lev_act (hϖ : Irreducible ϖ) (L M : FullLattice R K) (u : Rˣ) (i : ℤ) :
    lev hϖ (FullLattice.act (scalarGL (Units.map (algebraMap R K : R →* K) u * piU (K := K) hϖ ^ i)) L) M =
      lev hϖ L M + i := by
  apply lev_eq_of
  have key : ∀ n : ℤ, (FullLattice.act (scalarGL (Units.map (algebraMap R K : R →* K) u * piU (K := K) hϖ ^ i)) L).1 ≤
      vchain hϖ M.1 (n + i) ↔ L.1 ≤ vchain hϖ M.1 n := by
    intro n
    show latticeMap (scalarGL (Units.map (algebraMap R K : R →* K) u * piU (K := K) hϖ ^ i)) L.1 ≤ _ ↔ _
    rw [add_comm, vchain_add, mul_comm, ← sc_sc, latticeMap_scalarGL_map_units]
    exact ⟨le_of_latticeMap_le _, latticeMap_mono _⟩
  refine ⟨(key _).2 (lev_spec hϖ L M).1, fun h => (lev_spec hϖ L M).2 ((key _).1 ?_)⟩
  rwa [add_right_comm] at h

end Scaling

section Push

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def push (c : Kˣ) (L P : FullLattice 𝒪 K) (h : latticeMap (scalarGL c) L.1 ≤ P.1) :
    latticeBaseChange 𝒪 K B L →ₗ[B] latticeBaseChange 𝒪 K B P :=
  inclBaseChange B (M' := FullLattice.act (scalarGL c) L) (M := P) h ∘ₗ (actBaseChange B (scalarGL c) L).toLinearMap

theorem smul_mem_of_le {c : Kˣ} {L P : FullLattice 𝒪 K} (h : latticeMap (scalarGL c) L.1 ≤ P.1) (w : ↥L.1) :
    (c : K) • (w : Fin 2 → K) ∈ P.1 :=
  h (mem_latticeMap_scalarGL.mpr ⟨w, w.2, rfl⟩)

theorem inclBaseChange_tmul {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) (b : B) (v : ↥M₁.1) :
    inclBaseChange B h (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) :=
  rfl

theorem push_tmul (c : Kˣ) (L P : FullLattice 𝒪 K) (h : latticeMap (scalarGL c) L.1 ≤ P.1) (b : B) (w : ↥L.1) :
    push B c L P h (b ⊗ₜ[𝒪] w) = b ⊗ₜ[𝒪] (⟨(c : K) • (w : Fin 2 → K), smul_mem_of_le h w⟩ : ↥P.1) := by
  show inclBaseChange B (M' := FullLattice.act (scalarGL c) L) (M := P) h
    (b ⊗ₜ[𝒪] latticeMapEquiv (scalarGL c) L.1 w) = _
  erw [inclBaseChange_tmul]
  congr 1
  apply Subtype.ext
  show ((scalarGL c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec (w : Fin 2 → K) = (c : K) • (w : Fin 2 → K)
  exact scalarGL_mulVec c w

theorem algebraMap_smul_one_tmul {L : FullLattice 𝒪 K} (r : 𝒪) (y : ↥L.1) :
    (algebraMap 𝒪 B r • (1 : B)) ⊗ₜ[𝒪] y = (1 : B) ⊗ₜ[𝒪] (r • y) := by
  rw [smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]

theorem ext_one_tmul {L : FullLattice 𝒪 K} {X : Type} [AddCommGroup X] [Module B X]
    {f g : latticeBaseChange 𝒪 K B L →ₗ[B] X} (h : ∀ w : ↥L.1, f ((1 : B) ⊗ₜ[𝒪] w) = g ((1 : B) ⊗ₜ[𝒪] w)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul b w =>
      have hb : b ⊗ₜ[𝒪] w = b • ((1 : B) ⊗ₜ[𝒪] w) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [hb, map_smul, map_smul, h w]

theorem push_one_apply (L : FullLattice 𝒪 K) (h : latticeMap (scalarGL 1) L.1 ≤ L.1) (x : latticeBaseChange 𝒪 K B L) :
    push B 1 L L h x = x := by
  have key : push B 1 L L h = LinearMap.id := by
    apply ext_one_tmul
    intro w
    rw [push_tmul, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    show ((1 : Kˣ) : K) • (w : Fin 2 → K) = w
    rw [Units.val_one, one_smul]
  rw [key, LinearMap.id_apply]

theorem push_inclBaseChange (c : Kˣ) {L' L : FullLattice 𝒪 K} (hL : L'.1 ≤ L.1) (P : FullLattice 𝒪 K)
    (h : latticeMap (scalarGL c) L.1 ≤ P.1) (h' : latticeMap (scalarGL c) L'.1 ≤ P.1) (x : latticeBaseChange 𝒪 K B L') :
    push B c L P h (inclBaseChange B hL x) = push B c L' P h' x := by
  have key : push B c L P h ∘ₗ inclBaseChange B hL = push B c L' P h' := by
    apply ext_one_tmul
    intro w
    rw [LinearMap.comp_apply, inclBaseChange_tmul, push_tmul, push_tmul]
  rw [← key, LinearMap.comp_apply]

theorem inclBaseChange_push (c : Kˣ) (L : FullLattice 𝒪 K) {P P' : FullLattice 𝒪 K} (hP : P.1 ≤ P'.1)
    (h : latticeMap (scalarGL c) L.1 ≤ P.1) (h' : latticeMap (scalarGL c) L.1 ≤ P'.1) (x : latticeBaseChange 𝒪 K B L) :
    inclBaseChange B hP (push B c L P h x) = push B c L P' h' x := by
  have key : inclBaseChange B hP ∘ₗ push B c L P h = push B c L P' h' := by
    apply ext_one_tmul
    intro w
    rw [LinearMap.comp_apply, push_tmul, push_tmul, inclBaseChange_tmul]
  rw [← key, LinearMap.comp_apply]

theorem push_actBaseChange (c₂ c : Kˣ) (L P : FullLattice 𝒪 K)
    (h : latticeMap (scalarGL c₂) (FullLattice.act (scalarGL c) L).1 ≤ P.1) (h' : latticeMap (scalarGL (c₂ * c)) L.1 ≤ P.1)
    (x : latticeBaseChange 𝒪 K B L) :
    push B c₂ (FullLattice.act (scalarGL c) L) P h (actBaseChange B (scalarGL c) L x) = push B (c₂ * c) L P h' x := by
  have key : push B c₂ (FullLattice.act (scalarGL c) L) P h ∘ₗ (actBaseChange B (scalarGL c) L).toLinearMap =
      push B (c₂ * c) L P h' := by
    apply ext_one_tmul
    intro w
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, actBaseChange_tmul, push_tmul]
    erw [push_tmul]
    congr 1
    apply Subtype.ext
    show (c₂ : K) • (((scalarGL c : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).mulVec (w : Fin 2 → K)) =
      ((c₂ * c : Kˣ) : K) • (w : Fin 2 → K)
    rw [scalarGL_mulVec, smul_smul, Units.val_mul]
  rw [← key, LinearMap.comp_apply, LinearEquiv.coe_coe]

theorem push_eq_smul_push (c c' : Kˣ) (r : 𝒪) (hr : (c : K) = algebraMap 𝒪 K r * (c' : K)) (L P : FullLattice 𝒪 K)
    (h : latticeMap (scalarGL c) L.1 ≤ P.1) (h' : latticeMap (scalarGL c') L.1 ≤ P.1) (x : latticeBaseChange 𝒪 K B L) :
    push B c L P h x = algebraMap 𝒪 B r • push B c' L P h' x := by
  have key : push B c L P h = algebraMap 𝒪 B r • push B c' L P h' := by
    apply ext_one_tmul
    intro w
    rw [push_tmul, LinearMap.smul_apply, push_tmul, smul_tmul', algebraMap_smul_one_tmul]
    congr 1
    apply Subtype.ext
    show (c : K) • (w : Fin 2 → K) = ((r • (⟨(c' : K) • (w : Fin 2 → K), smul_mem_of_le h' w⟩ : ↥P.1) : ↥P.1) : Fin 2 → K)
    rw [Submodule.coe_smul, hr, mul_smul, algebraMap_smul]
  rw [key, LinearMap.smul_apply]

abbrev sigma {M' M : FullLattice 𝒪 K} (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M' :=
  ((smulInto π hπM).baseChange B :
    latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M')

theorem sigma_tmul {M' M : FullLattice 𝒪 K} (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1) (b : B) (v : ↥M.1) :
    sigma π B hπM (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪] (⟨algebraMap 𝒪 K π • (v : Fin 2 → K), hπM v v.2⟩ : ↥M'.1) := by
  rw [sigma, LinearMap.baseChange_tmul]
  rfl

theorem push_eq_smul_sigma_push {M' M : FullLattice 𝒪 K} (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (c c' : Kˣ) (r : 𝒪) (hr : (c : K) = algebraMap 𝒪 K r * (algebraMap 𝒪 K π * (c' : K))) (L : FullLattice 𝒪 K)
    (h : latticeMap (scalarGL c) L.1 ≤ M'.1) (h' : latticeMap (scalarGL c') L.1 ≤ M.1) (x : latticeBaseChange 𝒪 K B L) :
    push B c L M' h x = algebraMap 𝒪 B r • sigma π B hπM (push B c' L M h' x) := by
  have key : push B c L M' h = algebraMap 𝒪 B r • (sigma π B hπM ∘ₗ push B c' L M h') := by
    apply ext_one_tmul
    intro w
    rw [push_tmul, LinearMap.smul_apply, LinearMap.comp_apply, push_tmul, sigma_tmul, smul_tmul', algebraMap_smul_one_tmul]
    congr 1
    apply Subtype.ext
    show (c : K) • (w : Fin 2 → K) =
      ((r • (⟨algebraMap 𝒪 K π • ((c' : K) • (w : Fin 2 → K)), _⟩ : ↥M'.1) : ↥M'.1) : Fin 2 → K)
    rw [Submodule.coe_smul, hr, mul_smul, mul_smul, algebraMap_smul]
  rw [key, LinearMap.smul_apply, LinearMap.comp_apply]

theorem sigma_push {M' M : FullLattice 𝒪 K} (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (c c' : Kˣ) (hr : (c : K) = algebraMap 𝒪 K π * (c' : K)) (L : FullLattice 𝒪 K)
    (h : latticeMap (scalarGL c) L.1 ≤ M'.1) (h' : latticeMap (scalarGL c') L.1 ≤ M.1) (x : latticeBaseChange 𝒪 K B L) :
    sigma π B hπM (push B c' L M h' x) = push B c L M' h x := by
  rw [push_eq_smul_sigma_push π B hπM c c' 1 (by rw [map_one, one_mul]; exact hr) L h h', map_one, one_smul]

end Push

section Ext

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K]
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

structure ED (π : 𝒪) (B : Type) [CommRing B] [Algebra 𝒪 B] (M' M : FullLattice 𝒪 K) where
  N : Submodule B (latticeBaseChange 𝒪 K B M)
  N' : Submodule B (latticeBaseChange 𝒪 K B M')
  hle : M'.1 ≤ M.1
  hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1
  inv : Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)
  inv' : Module.Invertible B (latticeBaseChange 𝒪 K B M' ⧸ N')
  hmono : N'.map (inclBaseChange B hle) ≤ N
  hsmul : N.map (sigma π B hπM) ≤ N'
  h₁ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
    (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))
  h₂ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
    (1 : B) ⊗ₜ[𝒪] v' ∉ N' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))

variable {π : 𝒪}

def IsNorm (hπ : Irreducible π) (M : FullLattice 𝒪 K) (c : Kˣ) (L : FullLattice 𝒪 K) : Prop :=
  latticeMap (scalarGL c) L.1 ≤ M.1 ∧ ¬ latticeMap (scalarGL c) L.1 ≤ latticeMap (scalarGL (piU (K := K) hπ)) M.1

def nc (hπ : Irreducible π) (M L : FullLattice 𝒪 K) : Kˣ := piU (K := K) hπ ^ (-lev hπ L M)

theorem sc_zpow_neg_sc_zpow (hπ : Irreducible π) (j : ℤ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (piU (K := K) hπ ^ (-j))) (latticeMap (scalarGL (piU (K := K) hπ ^ j)) X) = X := by
  rw [sc_sc, zpow_neg, inv_mul_cancel, scalarGL_one, latticeMap_one]

theorem sc_zpow_sc_zpow_neg (hπ : Irreducible π) (j : ℤ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (piU (K := K) hπ ^ j)) (latticeMap (scalarGL (piU (K := K) hπ ^ (-j))) X) = X := by
  rw [sc_sc, zpow_neg, mul_inv_cancel, scalarGL_one, latticeMap_one]

theorem isNorm_nc (hπ : Irreducible π) (M L : FullLattice 𝒪 K) : IsNorm hπ M (nc hπ M L) L := by
  obtain ⟨h1, h2⟩ := lev_spec hπ L M
  constructor
  · have h3 := latticeMap_mono (R := 𝒪) (scalarGL (piU (K := K) hπ ^ (-lev hπ L M))) h1
    rw [vchain, sc_zpow_neg_sc_zpow] at h3
    exact h3
  · intro h
    apply h2
    have h3 := latticeMap_mono (R := 𝒪) (scalarGL (piU (K := K) hπ ^ (lev hπ L M))) h
    have e : latticeMap (scalarGL (piU (K := K) hπ ^ lev hπ L M)) (latticeMap (scalarGL (piU (K := K) hπ)) M.1) =
        vchain hπ M.1 (lev hπ L M + 1) := by
      rw [vchain, sc_sc, zpow_add_one]
    rw [nc, sc_zpow_sc_zpow_neg, e] at h3
    exact h3

theorem sc_units_mul (u : 𝒪ˣ) (c : Kˣ) (X : Submodule 𝒪 (Fin 2 → K)) :
    latticeMap (scalarGL (Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * c)) X = latticeMap (scalarGL c) X := by
  rw [mul_comm, ← sc_sc, latticeMap_scalarGL_map_units]

theorem lev_eq_of_isNorm (hπ : Irreducible π) (M L : FullLattice 𝒪 K) (u : 𝒪ˣ) (i : ℤ)
    (h : IsNorm hπ M (Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * piU (K := K) hπ ^ i) L) : lev hπ L M = -i := by
  obtain ⟨h1, h2⟩ := h
  rw [sc_units_mul] at h1 h2
  apply lev_eq_of
  constructor
  · have h3 := latticeMap_mono (R := 𝒪) (scalarGL (piU (K := K) hπ ^ (-i))) h1
    rw [sc_zpow_neg_sc_zpow] at h3
    exact h3
  · intro h
    apply h2
    have h3 := latticeMap_mono (R := 𝒪) (scalarGL (piU (K := K) hπ ^ i)) h
    rw [← vchain_add, show i + (-i + 1) = 1 by ring, vchain, zpow_one] at h3
    exact h3

theorem coe_nc_eq_of_lev_add (hπ : Irreducible π) (M L L' : FullLattice 𝒪 K) (k : ℕ)
    (hk : lev hπ L M + k = lev hπ L' M) :
    ((nc hπ M L : Kˣ) : K) = algebraMap 𝒪 K (π ^ k) * ((nc hπ M L' : Kˣ) : K) := by
  rw [nc, nc, ← hk, ← piU_pow_coe hπ, ← Units.val_mul, ← zpow_natCast, ← zpow_add]
  congr 2
  ring

namespace ED

variable {M' M : FullLattice 𝒪 K} (hπ : Irreducible π) (E : ED (K := K) π B M' M)

def lineAux (c : Kˣ) (L : FullLattice 𝒪 K) : Submodule B (latticeBaseChange 𝒪 K B L) := by
  classical
  exact if h' : latticeMap (scalarGL c) L.1 ≤ M'.1 then E.N'.comap (push B c L M' h')
    else if h : latticeMap (scalarGL c) L.1 ≤ M.1 then E.N.comap (push B c L M h) else ⊤

def lineFn (L : FullLattice 𝒪 K) : Submodule B (latticeBaseChange 𝒪 K B L) := E.lineAux (nc hπ M L) L

theorem lineAux_pos (c : Kˣ) (L : FullLattice 𝒪 K) (h' : latticeMap (scalarGL c) L.1 ≤ M'.1) :
    E.lineAux c L = E.N'.comap (push B c L M' h') := by
  unfold lineAux
  rw [dif_pos h']

theorem lineAux_neg (c : Kˣ) (L : FullLattice 𝒪 K) (h' : ¬ latticeMap (scalarGL c) L.1 ≤ M'.1)
    (h : latticeMap (scalarGL c) L.1 ≤ M.1) : E.lineAux c L = E.N.comap (push B c L M h) := by
  unfold lineAux
  rw [dif_neg h', dif_pos h]

theorem mem_lineAux_iff (c : Kˣ) (L : FullLattice 𝒪 K) (hcM : latticeMap (scalarGL c) L.1 ≤ M.1)
    (s : latticeBaseChange 𝒪 K B L) :
    s ∈ E.lineAux c L ↔ (∀ h' : latticeMap (scalarGL c) L.1 ≤ M'.1, push B c L M' h' s ∈ E.N') ∧
      (¬ latticeMap (scalarGL c) L.1 ≤ M'.1 → push B c L M hcM s ∈ E.N) := by
  by_cases h' : latticeMap (scalarGL c) L.1 ≤ M'.1
  · rw [E.lineAux_pos c L h', Submodule.mem_comap]
    exact ⟨fun h => ⟨fun _ => h, fun hn => absurd h' hn⟩, fun h => h.1 h'⟩
  · rw [E.lineAux_neg c L h' hcM, Submodule.mem_comap]
    exact ⟨fun h => ⟨fun hp => absurd hp h', fun _ => h⟩, fun h => h.2 h'⟩

theorem push_mem_N (c : Kˣ) (L : FullLattice 𝒪 K) (hcM : latticeMap (scalarGL c) L.1 ≤ M.1)
    (s : latticeBaseChange 𝒪 K B L) (hs : s ∈ E.lineAux c L) : push B c L M hcM s ∈ E.N := by
  rw [E.mem_lineAux_iff c L hcM] at hs
  by_cases h' : latticeMap (scalarGL c) L.1 ≤ M'.1
  · rw [← inclBaseChange_push B c L E.hle h' hcM]
    exact E.hmono (Submodule.mem_map_of_mem (hs.1 h'))
  · exact hs.2 h'

theorem push_mem_N' (c : Kˣ) (L : FullLattice 𝒪 K) (h' : latticeMap (scalarGL c) L.1 ≤ M'.1)
    (s : latticeBaseChange 𝒪 K B L) (hs : s ∈ E.lineAux c L) : push B c L M' h' s ∈ E.N' := by
  rw [E.mem_lineAux_iff c L (h'.trans E.hle)] at hs
  exact hs.1 h'

theorem lineAux_units_mul (u : 𝒪ˣ) (c : Kˣ) (L : FullLattice 𝒪 K) (hcM : latticeMap (scalarGL c) L.1 ≤ M.1) :
    E.lineAux (Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * c) L = E.lineAux c L := by
  have hEq : latticeMap (scalarGL (Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * c)) L.1 = latticeMap (scalarGL c) L.1 :=
    sc_units_mul u c L.1
  have hcM' : latticeMap (scalarGL (Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * c)) L.1 ≤ M.1 := hEq ▸ hcM
  have hr : ((Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * c : Kˣ) : K) = algebraMap 𝒪 K u * (c : K) := by
    rw [Units.val_mul, Units.coe_map, MonoidHom.coe_coe]
  have hu : IsUnit (algebraMap 𝒪 B (u : 𝒪)) := u.isUnit.map _
  ext s
  rw [E.mem_lineAux_iff _ L hcM', E.mem_lineAux_iff c L hcM]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have := hA (hEq ▸ h')
      rwa [push_eq_smul_push B _ c (u : 𝒪) hr L M' (hEq ▸ h') h', smul_mem_iff_of_isUnit _ hu] at this
    · have := hB (fun h => h' (hEq ▸ h))
      rwa [push_eq_smul_push B _ c (u : 𝒪) hr L M hcM' hcM, smul_mem_iff_of_isUnit _ hu] at this
  · rintro ⟨hA, hB⟩
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · rw [push_eq_smul_push B _ c (u : 𝒪) hr L M' h' (hEq ▸ h'), smul_mem_iff_of_isUnit _ hu]
      exact hA (hEq ▸ h')
    · rw [push_eq_smul_push B _ c (u : 𝒪) hr L M hcM' hcM, smul_mem_iff_of_isUnit _ hu]
      exact hB (fun h => h' (hEq ▸ h))

theorem lineFn_eq_lineAux (c : Kˣ) (L : FullLattice 𝒪 K) (hc : IsNorm hπ M c L) : E.lineFn hπ L = E.lineAux c L := by
  obtain ⟨u, i, rfl⟩ := unit_zpow_decomp hπ c
  have hl := lev_eq_of_isNorm hπ M L u i hc
  show E.lineAux (piU (K := K) hπ ^ (-lev hπ L M)) L = _
  rw [hl, neg_neg]
  have hcM : latticeMap (scalarGL (piU (K := K) hπ ^ i)) L.1 ≤ M.1 := by
    have := hc.1; rwa [sc_units_mul] at this
  exact (E.lineAux_units_mul u _ L hcM).symm

theorem invertible_lineAux (c : Kˣ) (L : FullLattice 𝒪 K) (hc : IsNorm hπ M c L) :
    Module.Invertible B (latticeBaseChange 𝒪 K B L ⧸ E.lineAux c L) := by
  by_cases h' : latticeMap (scalarGL c) L.1 ≤ M'.1
  · rw [E.lineAux_pos c L h']
    haveI := E.inv'

    obtain ⟨y, hy, hyπ⟩ := Set.not_subset.mp hc.2
    obtain ⟨w₀, hw₀, rfl⟩ := mem_latticeMap_scalarGL.mp hy
    refine invertible_quot_comap _ _ (surjective_mkQ_comp_of_generator _ _ ((1 : B) ⊗ₜ[𝒪] (⟨w₀, hw₀⟩ : ↥L.1)) ?_)
    intro 𝔪 h𝔪
    rw [push_tmul]
    apply E.h₂ 𝔪 h𝔪.isPrime
    rintro ⟨w, hw⟩
    apply hyπ
    refine mem_latticeMap_scalarGL.mpr ⟨w, w.2, ?_⟩
    rw [piU_coe]
    exact hw.symm
  · rw [E.lineAux_neg c L h' hc.1]
    haveI := E.inv
    obtain ⟨y, hy, hyM'⟩ := Set.not_subset.mp h'
    obtain ⟨w₁, hw₁, rfl⟩ := mem_latticeMap_scalarGL.mp hy
    refine invertible_quot_comap _ _ (surjective_mkQ_comp_of_generator _ _ ((1 : B) ⊗ₜ[𝒪] (⟨w₁, hw₁⟩ : ↥L.1)) ?_)
    intro 𝔪 h𝔪
    rw [push_tmul]
    exact E.h₁ 𝔪 h𝔪.isPrime _ hyM'

theorem invertible_lineFn (L : FullLattice 𝒪 K) : Module.Invertible B (latticeBaseChange 𝒪 K B L ⧸ E.lineFn hπ L) :=
  E.invertible_lineAux hπ (nc hπ M L) L (isNorm_nc hπ M L)

theorem lineFn_self : E.lineFn hπ M = E.N := by
  have h1M : latticeMap (scalarGL (1 : Kˣ)) M.1 = M.1 := by rw [scalarGL_one, latticeMap_one]
  have hc : IsNorm hπ M 1 M := by
    refine ⟨h1M.le, ?_⟩
    rw [h1M]
    exact not_le_sc_pi hπ M
  rw [E.lineFn_eq_lineAux hπ 1 M hc]
  haveI := E.invertible_lineAux hπ 1 M hc
  haveI := E.inv
  apply eq_of_le_of_invertible
  intro s hs
  have h := E.push_mem_N 1 M hc.1 s hs
  rwa [push_one_apply] at h

theorem lineFn_self' : E.lineFn hπ M' = E.N' := by
  have hπK : ((piU (K := K) hπ : Kˣ) : K) = algebraMap 𝒪 K π := piU_coe hπ
  have hπM' : latticeMap (scalarGL (piU (K := K) hπ)) M.1 ≤ M'.1 :=
    (sc_le_iff _ _ _).2 fun w hw => by rw [hπK]; exact E.hπM w hw
  by_cases hd : M'.1 ≤ latticeMap (scalarGL (piU (K := K) hπ)) M.1
  ·
    have hc1 : latticeMap (scalarGL (piU (K := K) hπ)⁻¹) M'.1 ≤ M.1 := by
      have := latticeMap_mono (R := 𝒪) (scalarGL (piU (K := K) hπ)⁻¹) hd
      rwa [sc_sc, inv_mul_cancel, scalarGL_one, latticeMap_one] at this
    have hc : IsNorm hπ M (piU (K := K) hπ)⁻¹ M' := by
      refine ⟨hc1, fun h => not_le_sc_pi hπ M ?_⟩
      have h3 := latticeMap_mono (R := 𝒪) (scalarGL (piU (K := K) hπ)) h
      rw [sc_sc, mul_inv_cancel, scalarGL_one, latticeMap_one] at h3
      exact le_of_latticeMap_le _ (hπM'.trans h3)
    have hneg : ¬ latticeMap (scalarGL (piU (K := K) hπ)⁻¹) M'.1 ≤ M'.1 := by
      intro h
      apply not_le_sc_pi hπ M'
      have h3 := latticeMap_mono (R := 𝒪) (scalarGL (piU (K := K) hπ)) h
      rwa [sc_sc, mul_inv_cancel, scalarGL_one, latticeMap_one] at h3
    rw [E.lineFn_eq_lineAux hπ _ M' hc]
    haveI := E.invertible_lineAux hπ _ M' hc
    haveI := E.inv'
    apply eq_of_le_of_invertible
    intro s hs
    have h := E.push_mem_N _ M' hc.1 s hs
    have h1 : latticeMap (scalarGL (1 : Kˣ)) M'.1 ≤ M'.1 := by rw [scalarGL_one, latticeMap_one]
    have h2 : sigma π B E.hπM (push B (piU (K := K) hπ)⁻¹ M' M hc.1 s) = s := by
      rw [sigma_push π B E.hπM 1 (piU (K := K) hπ)⁻¹ ?_ M' h1 hc.1 s, push_one_apply]
      rw [← hπK, Units.val_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [← h2]
    exact E.hsmul (Submodule.mem_map_of_mem h)
  ·
    have h1M : latticeMap (scalarGL (1 : Kˣ)) M'.1 = M'.1 := by rw [scalarGL_one, latticeMap_one]
    have hc : IsNorm hπ M 1 M' := by
      refine ⟨h1M.le.trans E.hle, ?_⟩
      rw [h1M]
      exact hd
    rw [E.lineFn_eq_lineAux hπ 1 M' hc, E.lineAux_pos 1 M' h1M.le]
    ext s
    rw [Submodule.mem_comap, push_one_apply]

theorem lineFn_mono {L' L : FullLattice 𝒪 K} (hL : L'.1 ≤ L.1) :
    (E.lineFn hπ L').map (inclBaseChange B hL) ≤ E.lineFn hπ L := by
  obtain ⟨k, hk⟩ := Int.le.dest (lev_le_lev_of_le hπ M hL)
  have hcL := isNorm_nc hπ M L
  have hcL' := isNorm_nc hπ M L'
  have hr := coe_nc_eq_of_lev_add hπ M L L' k hk

  have hcL'M : latticeMap (scalarGL (nc hπ M L)) L'.1 ≤ M.1 := (latticeMap_mono _ hL).trans hcL.1
  rintro _ ⟨s', hs', rfl⟩
  change s' ∈ E.lineAux (nc hπ M L') L' at hs'
  show inclBaseChange B hL s' ∈ E.lineAux (nc hπ M L) L
  rw [E.mem_lineAux_iff _ L hcL.1]

  have hN : push B (nc hπ M L') L' M hcL'.1 s' ∈ E.N := E.push_mem_N _ L' hcL'.1 s' hs'
  refine ⟨fun h' => ?_, fun h' => ?_⟩
  ·
    have hcL'M' : latticeMap (scalarGL (nc hπ M L)) L'.1 ≤ M'.1 := (latticeMap_mono _ hL).trans h'
    rw [push_inclBaseChange B _ hL M' h' hcL'M']
    cases k with
    | zero =>

        have hcc : nc hπ M L' = nc hπ M L := by
          rw [nc, nc, ← hk, Nat.cast_zero, add_zero]
        rw [hcc] at hs'
        exact E.push_mem_N' _ L' hcL'M' s' hs'
    | succ k₀ =>
        have hr' : ((nc hπ M L : Kˣ) : K) = algebraMap 𝒪 K (π ^ k₀) * (algebraMap 𝒪 K π * ((nc hπ M L' : Kˣ) : K)) := by
          rw [hr, pow_succ, map_mul, mul_assoc]
        rw [push_eq_smul_sigma_push π B E.hπM _ _ (π ^ k₀) hr' L' hcL'M' hcL'.1 s']
        exact E.N'.smul_mem _ (E.hsmul (Submodule.mem_map_of_mem hN))
  ·
    rw [push_inclBaseChange B _ hL M hcL.1 hcL'M, push_eq_smul_push B _ _ (π ^ k) hr L' M hcL'M hcL'.1 s']
    exact E.N.smul_mem _ hN

theorem lineAux_act (c₂ c c₃ : Kˣ) (h3 : c₂ * c = c₃) (L : FullLattice 𝒪 K) (hcM : latticeMap (scalarGL c₃) L.1 ≤ M.1) :
    E.lineAux c₂ (FullLattice.act (scalarGL c) L) = (E.lineAux c₃ L).map (actBaseChange B (scalarGL c) L).toLinearMap := by
  have hEq : latticeMap (scalarGL c₂) (FullLattice.act (scalarGL c) L).1 = latticeMap (scalarGL c₃) L.1 := by
    show latticeMap (scalarGL c₂) (latticeMap (scalarGL c) L.1) = _
    rw [sc_sc, h3]
  have hcM₂ : latticeMap (scalarGL c₂) (FullLattice.act (scalarGL c) L).1 ≤ M.1 := hEq ▸ hcM
  subst h3
  ext x
  rw [Submodule.mem_map, E.mem_lineAux_iff c₂ _ hcM₂]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨(actBaseChange B (scalarGL c) L).symm x, ?_, LinearEquiv.apply_symm_apply _ _⟩
    rw [E.mem_lineAux_iff _ L hcM]
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · have := hA (hEq ▸ h')
      rwa [← LinearEquiv.apply_symm_apply (actBaseChange B (scalarGL c) L) x,
        push_actBaseChange B c₂ c L M' (hEq ▸ h') h'] at this
    · have := hB (fun h => h' (hEq ▸ h))
      rwa [← LinearEquiv.apply_symm_apply (actBaseChange B (scalarGL c) L) x,
        push_actBaseChange B c₂ c L M hcM₂ hcM] at this
  · rintro ⟨y, hy, rfl⟩
    rw [E.mem_lineAux_iff _ L hcM] at hy
    refine ⟨fun h' => ?_, fun h' => ?_⟩
    · rw [LinearEquiv.coe_coe, push_actBaseChange B c₂ c L M' h' (hEq ▸ h')]
      exact hy.1 (hEq ▸ h')
    · rw [LinearEquiv.coe_coe, push_actBaseChange B c₂ c L M hcM₂ hcM]
      exact hy.2 (fun h => h' (hEq ▸ h))

theorem lineFn_homothety (c : Kˣ) (L : FullLattice 𝒪 K) :
    E.lineFn hπ (FullLattice.act (scalarGL c) L) = (E.lineFn hπ L).map (actBaseChange B (scalarGL c) L).toLinearMap := by
  obtain ⟨u, i, rfl⟩ := unit_zpow_decomp hπ c
  show E.lineAux (piU (K := K) hπ ^ (-lev hπ (FullLattice.act _ L) M)) _ = (E.lineAux (nc hπ M L) L).map _
  rw [lev_act]
  have h3 : piU (K := K) hπ ^ (-(lev hπ L M + i)) * (Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * piU (K := K) hπ ^ i) =
      Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * nc hπ M L := by
    rw [nc, mul_left_comm, ← zpow_add]
    congr 2
    ring
  have hcM : latticeMap (scalarGL (Units.map (algebraMap 𝒪 K : 𝒪 →* K) u * nc hπ M L)) L.1 ≤ M.1 := by
    rw [sc_units_mul]
    exact (isNorm_nc hπ M L).1
  rw [E.lineAux_act _ _ _ h3 L hcM, E.lineAux_units_mul u _ L (isNorm_nc hπ M L).1]

def extDatum : DeligneDatum (K := K) π B where
  line L := E.lineFn hπ L
  invertible L := E.invertible_lineFn hπ L
  mono h := E.lineFn_mono hπ h
  homothety c L := E.lineFn_homothety hπ c L
  nondeg 𝔭 h𝔭 := by
    refine ⟨M', M, E.hle, fun v => E.hπM v v.2, ?_, ?_⟩
    · rw [E.lineFn_self hπ]
      exact E.h₁ 𝔭 h𝔭
    · rw [E.lineFn_self' hπ]
      exact E.h₂ 𝔭 h𝔭

theorem extDatum_line (L : FullLattice 𝒪 K) : (E.extDatum hπ).line L = E.lineFn hπ L := rfl

theorem extDatum_spec :
    (E.extDatum hπ).line M = E.N ∧ (E.extDatum hπ).line M' = E.N' ∧ (E.extDatum hπ).InEdgeChart π M' M := by
  refine ⟨E.lineFn_self hπ, E.lineFn_self' hπ, fun 𝔭 h𝔭 => ⟨E.hle, fun v => E.hπM v v.2, ?_, ?_⟩⟩
  · rw [extDatum_line, E.lineFn_self hπ]
    exact E.h₁ 𝔭 h𝔭
  · rw [extDatum_line, E.lineFn_self' hπ]
    exact E.h₂ 𝔭 h𝔭

end ED

end Ext

end P2mKcOmegaExt

end

open P2mKcOmegaExt in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    {M' M : FullLattice 𝒪 K} (hle : M'.1 ≤ M.1) (hπM : ∀ v ∈ M.1, algebraMap 𝒪 K π • v ∈ M'.1)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) (N' : Submodule B (latticeBaseChange 𝒪 K B M'))
    [Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ N)] [Module.Invertible B (latticeBaseChange 𝒪 K B M' ⧸ N')]
    (hmono : N'.map (inclBaseChange B hle) ≤ N)
    (hsmul : N.map ((smulInto π hπM).baseChange B :
      latticeBaseChange 𝒪 K B M →ₗ[B] latticeBaseChange 𝒪 K B M') ≤ N')
    (h₁ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
      (1 : B) ⊗ₜ[𝒪] v ∉ N ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)))
    (h₂ : ∀ 𝔭 : Ideal B, 𝔭.IsPrime → ∀ v' : ↥M'.1,
      (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = algebraMap 𝒪 K π • (w : Fin 2 → K)) →
      (1 : B) ⊗ₜ[𝒪] v' ∉ N' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) :
    ∃ d : DeligneDatum (K := K) π B, d.line M = N ∧ d.line M' = N' ∧ d.InEdgeChart π M' M :=
  let E : ED (K := K) π B M' M :=
    { N := N, N' := N', hle := hle, hπM := hπM, inv := ‹_›, inv' := ‹_›, hmono := hmono, hsmul := hsmul,
      h₁ := h₁, h₂ := h₂ }
  ⟨E.extDatum hπ, E.extDatum_spec hπ⟩

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_inEdgeChart_and_line_eq (solution)
