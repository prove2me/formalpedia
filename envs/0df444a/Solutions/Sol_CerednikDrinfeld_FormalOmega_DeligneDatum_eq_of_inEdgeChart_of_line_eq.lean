-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.eq_of_inEdgeChart_of_line_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/512efb20-7014-59f1-a6fc-e72b176fc1f6

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega TensorProduct

noncomputable section

namespace P2mKcOmegaForcing

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

end Generation

section Transitions

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem line_le_comap (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) :
    d.line M₁ ≤ (d.line M₂).comap (inclBaseChange B h) :=
  Submodule.map_le_iff_le_comap.mp (d.mono h)

def transition (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) :
    (latticeBaseChange 𝒪 K B M₁ ⧸ d.line M₁) →ₗ[B] (latticeBaseChange 𝒪 K B M₂ ⧸ d.line M₂) :=
  Submodule.mapQ _ _ (inclBaseChange B h) (line_le_comap π d h)

theorem transition_mk (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1)
    (x : latticeBaseChange 𝒪 K B M₁) :
    transition π d h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (inclBaseChange B h x) :=
  Submodule.mapQ_apply _ _ _ x

theorem inclBaseChange_tmul {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1) (b : B) (v : ↥M₁.1) :
    inclBaseChange B h (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) :=
  rfl

theorem line_eq_comap_of_generator (d : DeligneDatum (K := K) π B) {M₁ M₂ : FullLattice 𝒪 K} (h : M₁.1 ≤ M₂.1)
    (v : ↥M₁.1) (hv : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal →
      (1 : B) ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) ∉ d.line M₂ ⊔ (𝔪 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M₂))) :
    d.line M₁ = (d.line M₂).comap (inclBaseChange B h) := by
  haveI := d.invertible M₁
  haveI := d.invertible M₂
  apply le_antisymm (line_le_comap π d h)
  have hsurj : Function.Surjective (transition π d h) := by
    rw [← LinearMap.range_eq_top]
    apply eq_top_of_mem_of_forall_not_mem_smul_top _
      ((d.line M₂).mkQ ((1 : B) ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1)))
    · refine ⟨(d.line M₁).mkQ ((1 : B) ⊗ₜ[𝒪] v), ?_⟩
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, transition_mk, inclBaseChange_tmul]
    · intro 𝔪 h𝔪 hmem
      exact hv 𝔪 h𝔪 (mem_sup_smul_top_of_mkQ_mem _ _ _ hmem)
  have hinj := (Module.Invertible.bijective_of_surjective hsurj).1
  intro x hx
  rw [Submodule.mem_comap] at hx
  have h0 : transition π d h (Submodule.Quotient.mk x) = 0 := by
    rw [transition_mk]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have h1 : (Submodule.Quotient.mk x : latticeBaseChange 𝒪 K B M₁ ⧸ d.line M₁) = 0 :=
    hinj (by rw [h0, map_zero])
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

theorem line_eq_of_line_le (d d' : DeligneDatum (K := K) π B) (L : FullLattice 𝒪 K) (hle : d'.line L ≤ d.line L) :
    d'.line L = d.line L := by
  haveI := d.invertible L
  haveI := d'.invertible L
  apply le_antisymm hle
  have hle' : d'.line L ≤ (d.line L).comap (LinearMap.id : latticeBaseChange 𝒪 K B L →ₗ[B] _) := by
    rw [Submodule.comap_id]; exact hle
  let f : (latticeBaseChange 𝒪 K B L ⧸ d'.line L) →ₗ[B] (latticeBaseChange 𝒪 K B L ⧸ d.line L) :=
    Submodule.mapQ _ _ LinearMap.id hle'
  have hf : ∀ x, f (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := fun x => Submodule.mapQ_apply _ _ _ x
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk x, hf x⟩
  have hinj := (Module.Invertible.bijective_of_surjective hsurj).1
  intro x hx
  have h0 : f (Submodule.Quotient.mk x) = 0 := by
    rw [hf]; exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have h1 : (Submodule.Quotient.mk x : latticeBaseChange 𝒪 K B L ⧸ d'.line L) = 0 :=
    hinj (by rw [h0, map_zero])
  exact (Submodule.Quotient.mk_eq_zero _).mp h1

theorem line_eq_of_line_act_eq (d d' : DeligneDatum (K := K) π B) (c : Kˣ) (L : FullLattice 𝒪 K)
    (h : d'.line (FullLattice.act (scalarGL c) L) = d.line (FullLattice.act (scalarGL c) L)) :
    d'.line L = d.line L := by
  rw [d.homothety c L, d'.homothety c L] at h
  exact Submodule.map_injective_of_injective (actBaseChange B (scalarGL c) L).injective h

end Transitions

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

theorem exists_sc_le_not_le (hϖ : Irreducible ϖ) {L M : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (hM : IsFullLattice M) :
    ∃ c : Kˣ, latticeMap (scalarGL c) L ≤ M ∧
      ¬ latticeMap (scalarGL c) L ≤ latticeMap (scalarGL (piU (K := K) hϖ)) M := by
  obtain ⟨a, ha⟩ := exists_sc_pow_le hϖ hM hL

  have hne : ∃ v ∈ latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L, v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hbot : latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L = ⊥ := by
      rw [eq_bot_iff]; intro v hv; rw [Submodule.mem_bot]; exact hcon v hv
    have hfull := hL.map (scalarGL (piU (K := K) hϖ ^ a))
    have htop := hfull.2
    rw [hbot] at htop

    have hbt : (⊤ : Submodule K (Fin 2 → K)) = ⊥ := by
      rw [← htop, Submodule.span_eq_bot]
      intro x hx
      rw [SetLike.mem_coe, Submodule.mem_bot] at hx
      exact hx
    exact top_ne_bot hbt
  obtain ⟨v, hv, hv0⟩ := hne
  obtain ⟨b, hb⟩ := exists_not_mem_sc_pow hϖ hM hv0

  classical
  have hex : ∃ j : ℕ, ¬ latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L ≤
      latticeMap (scalarGL (piU (K := K) hϖ ^ j)) M := ⟨b, fun h => hb (h hv)⟩
  set j := Nat.find hex with hj_def
  have hj : ¬ latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L ≤ latticeMap (scalarGL (piU (K := K) hϖ ^ j)) M :=
    Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    apply hj
    rw [h0, pow_zero, scalarGL_one, latticeMap_one]
    exact ha
  obtain ⟨i, hi'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
  have hi : j = i + 1 := hi'
  clear hi'
  have hi' : latticeMap (scalarGL (piU (K := K) hϖ ^ a)) L ≤ latticeMap (scalarGL (piU (K := K) hϖ ^ i)) M := by
    have := Nat.find_min hex (show i < Nat.find hex by rw [← hj_def, hi]; exact Nat.lt_succ_self i)
    push Not at this
    exact this

  refine ⟨(piU (K := K) hϖ ^ i)⁻¹ * piU (K := K) hϖ ^ a, ?_, ?_⟩
  · have h1 := latticeMap_mono (R := R) (scalarGL (piU (K := K) hϖ ^ i)⁻¹) hi'
    rw [sc_sc, sc_sc, inv_mul_cancel, scalarGL_one, latticeMap_one] at h1
    exact h1
  · intro hcon
    apply hj
    have h1 := latticeMap_mono (R := R) (scalarGL (piU (K := K) hϖ ^ i)) hcon
    rw [sc_sc, sc_sc, ← mul_assoc, mul_inv_cancel, one_mul, ← pow_succ, ← hi] at h1
    exact h1

end Scaling

section Forcing

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
  [IsFractionRing 𝒪 K] {π : 𝒪}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem line_eq_of_generator (d d' : DeligneDatum (K := K) π B) {L₁ M₂ : FullLattice 𝒪 K} (h : L₁.1 ≤ M₂.1)
    (hM₂ : d'.line M₂ = d.line M₂) (v : ↥L₁.1)
    (hv : ∀ 𝔪 : Ideal B, 𝔪.IsMaximal →
      (1 : B) ⊗ₜ[𝒪] (⟨v, h v.2⟩ : ↥M₂.1) ∉ d.line M₂ ⊔ (𝔪 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M₂))) :
    d'.line L₁ = d.line L₁ := by
  apply line_eq_of_line_le π d d' L₁
  rw [line_eq_comap_of_generator π d h v hv, ← hM₂]
  exact line_le_comap π d' h

theorem forcing (hπ : Irreducible π) (d d' : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K)
    (h : d.InEdgeChart π M' M) (hM : d'.line M = d.line M) (hM' : d'.line M' = d.line M') : d' = d := by
  apply DeligneDatum.ext'
  funext L

  obtain ⟨c, hcM, hcπM⟩ := exists_sc_le_not_le (K := K) hπ L.2 M.2
  apply line_eq_of_line_act_eq π d d' c L
  set L₁ : FullLattice 𝒪 K := FullLattice.act (scalarGL c) L with hL₁
  have hL₁M : L₁.1 ≤ M.1 := hcM
  by_cases hcase : L₁.1 ≤ M'.1
  ·
    obtain ⟨v, hvL, hvπ⟩ := Set.not_subset.mp hcπM
    refine line_eq_of_generator d d' hcase hM' ⟨v, hvL⟩ fun 𝔪 h𝔪 => ?_
    obtain ⟨-, -, -, h2⟩ := h 𝔪 h𝔪.isPrime
    apply h2 ⟨v, hcase hvL⟩
    rintro ⟨w, hw⟩
    apply hvπ
    exact mem_latticeMap_scalarGL.mpr ⟨w, w.2, by rw [piU_coe]; exact hw.symm⟩
  ·
    obtain ⟨v, hvL, hvM'⟩ := Set.not_subset.mp hcase
    refine line_eq_of_generator d d' hL₁M hM ⟨v, hvL⟩ fun 𝔪 h𝔪 => ?_
    obtain ⟨-, -, h1, -⟩ := h 𝔪 h𝔪.isPrime
    exact h1 ⟨v, hL₁M hvL⟩ hvM'

end Forcing

end P2mKcOmegaForcing

end

open P2mKcOmegaForcing in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d d' : DeligneDatum (K := K) π B) (M' M : FullLattice 𝒪 K) (h : d.InEdgeChart π M' M)
    (hM : d'.line M = d.line M) (hM' : d'.line M' = d.line M') : d' = d :=
  forcing hπ d d' M' M h hM hM'

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_eq_of_inEdgeChart_of_line_eq (solution)
