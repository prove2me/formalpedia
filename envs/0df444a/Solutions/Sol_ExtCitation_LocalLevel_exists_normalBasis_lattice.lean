-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_normalBasis_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dd4a5830-cabb-5f71-ba7b-090603378595

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Theorems.Thm_ExtCitation_LocalLevel_mem_Rw_iff_isIntegral
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Theorems.Thm_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_normalBasis_lattice

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
open ExtCitation.LocalLevel
open scoped NNReal

namespace Ws26T4D
open ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

theorem mem_Rw_iff_norm_le_one (x : Kw) : x ∈ Rw q Kw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  rw [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, PadicAlgCl.valuation_def]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem norm_coe_eq_spectralNorm (x : Kw) : ‖(x : PadicAlgCl q)‖ = spectralNorm ℚ_[q] Kw x := by
  rw [spectralNorm.eq_of_tower (L := PadicAlgCl q), PadicAlgCl.spectralNorm_eq]; rfl

end Ws26T4D

namespace Ws26T4

open ExtCitation.LocalLevel IsLocalRing

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

scoped instance isScalarTower_int : IsScalarTower ℤ_[q] Kw (PadicAlgCl q) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem mem_Rw_iff_mem_integralClosure (x : Kw) : x ∈ Rw q Kw ↔ x ∈ integralClosure ℤ_[q] Kw := by
  rw [mem_Rw_iff_isIntegral, mem_integralClosure_iff,
    show ((x : Kw) : PadicAlgCl q) = algebraMap Kw (PadicAlgCl q) x from rfl,
    isIntegral_algebraMap_iff (algebraMap Kw (PadicAlgCl q)).injective]

noncomputable def intClosureEquivRw : integralClosure ℤ_[q] Kw ≃+* Rw q Kw where
  toFun x := ⟨x.1, (mem_Rw_iff_mem_integralClosure q Kw x.1).mpr x.2⟩
  invFun x := ⟨x.1, (mem_Rw_iff_mem_integralClosure q Kw x.1).mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[scoped simp] theorem coe_intClosureEquivRw (x : integralClosure ℤ_[q] Kw) :
    ((intClosureEquivRw q Kw x : Rw q Kw) : Kw) = (x : Kw) := rfl

theorem norm_natCast_q : ‖((q : ℕ) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)), PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_eq_one_of_isUnit {x : Rw q Kw} (hx : IsUnit x) : ‖((x : Kw) : PadicAlgCl q)‖ = 1 := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  have hx1 : ‖((x : Kw) : PadicAlgCl q)‖ ≤ 1 := by exact_mod_cast (mem_padicIntegers_iff q).mp x.2
  have hu1 : ‖((u : Kw) : PadicAlgCl q)‖ ≤ 1 := by exact_mod_cast (mem_padicIntegers_iff q).mp u.2
  have hprod : ‖((x : Kw) : PadicAlgCl q)‖ * ‖((u : Kw) : PadicAlgCl q)‖ = 1 := by
    rw [← norm_mul]
    have := congrArg (fun t : Rw q Kw => ((t : Kw) : PadicAlgCl q)) hu
    push_cast at this
    rw [this, norm_one]
  nlinarith [norm_nonneg ((x : Kw) : PadicAlgCl q), norm_nonneg ((u : Kw) : PadicAlgCl q)]

theorem natCast_mem_maximalIdeal : ((q : ℕ) : Rw q Kw) ∈ maximalIdeal (Rw q Kw) := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  intro h
  have h1 := norm_eq_one_of_isUnit q Kw h
  push_cast at h1
  rw [norm_natCast_q] at h1
  have : (1 : ℝ) < q := by exact_mod_cast (Fact.out : q.Prime).one_lt
  rw [inv_eq_one] at h1
  exact absurd h1 (by exact_mod_cast (Fact.out : q.Prime).one_lt.ne')

theorem natCast_ne_zero : ((q : ℕ) : Rw q Kw) ≠ 0 := by
  intro h
  have := congrArg (fun t : Rw q Kw => (t : Kw)) h
  push_cast at this
  exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) this

theorem smodEq_pow_top_iff {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD I ^ n • (⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

theorem isAdicComplete_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (e : A ≃+* B) [IsAdicComplete (maximalIdeal A) A] :
    IsAdicComplete (maximalIdeal B) B := by

  have hmap : Ideal.map (e : A →+* B) (maximalIdeal A) = maximalIdeal B := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro z hz
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at hz
      intro hu; exact hz (by simpa using hu.map (e.symm : B →+* A))
    · intro z hz
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      rw [mem_maximalIdeal, mem_nonunits_iff] at hz
      intro hu; exact hz (by simpa using hu.map (e : A →+* B))
  have hmem : ∀ (n : ℕ) (z : B), z ∈ maximalIdeal B ^ n ↔ e.symm z ∈ maximalIdeal A ^ n := by
    intro n z
    rw [← hmap, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  have hA : IsHausdorff (maximalIdeal A) A := inferInstance
  have hA' : IsPrecomplete (maximalIdeal A) A := inferInstance
  haveI : IsHausdorff (maximalIdeal B) B := by
    refine ⟨fun z hz => ?_⟩
    have h0 : e.symm z = 0 := by
      refine IsHausdorff.haus hA _ fun n => ?_
      rw [smodEq_pow_top_iff, sub_zero, ← hmem]
      have := hz n
      rwa [smodEq_pow_top_iff, sub_zero] at this
    simpa using congrArg e h0
  haveI : IsPrecomplete (maximalIdeal B) B := by
    refine ⟨fun f hf => ?_⟩
    have hg : ∀ {m n : ℕ}, m ≤ n →
        e.symm (f m) ≡ e.symm (f n) [SMOD maximalIdeal A ^ m • (⊤ : Submodule A A)] := by
      intro m n hmn
      rw [smodEq_pow_top_iff, ← map_sub, ← hmem]
      exact (smodEq_pow_top_iff (maximalIdeal B) m _ _).mp (hf hmn)
    obtain ⟨L, hL⟩ := IsPrecomplete.prec hA' hg
    refine ⟨e L, fun n => ?_⟩
    rw [smodEq_pow_top_iff, hmem, map_sub, RingEquiv.symm_apply_apply]
    exact (smodEq_pow_top_iff (maximalIdeal A) n _ _).mp (hL n)
  exact IsAdicComplete.mk

theorem isLocalHom_algebraMap_intClosure [IsLocalRing (integralClosure ℤ_[q] Kw)] :
    IsLocalHom (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw)) := by
  refine ⟨fun z hz => ?_⟩

  have hu : IsUnit (intClosureEquivRw q Kw (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw) z)) :=
    hz.map (intClosureEquivRw q Kw)
  have h1 := norm_eq_one_of_isUnit q Kw hu
  rw [coe_intClosureEquivRw] at h1
  have h2 : ((algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw) z : Kw) : PadicAlgCl q)
      = algebraMap ℚ_[q] (PadicAlgCl q) (z : ℚ_[q]) := rfl
  rw [h2, PadicAlgCl.norm_extends] at h1
  exact PadicInt.isUnit_iff.mpr h1

end Ws26T4
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_normalBasis_lattice.Ws26T4"

namespace Ws26T4
open ExtCitation.LocalLevel IsLocalRing

variable (q : ℕ) [Fact q.Prime] (Kw : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] Kw]

@[reducible] noncomputable def algInt : Algebra ℤ_[q] (Rw q Kw) :=
  ((intClosureEquivRw q Kw).toRingHom.comp (algebraMap ℤ_[q] (integralClosure ℤ_[q] Kw))).toAlgebra

attribute [local instance] algInt

theorem algebraMap_int_coe (z : ℤ_[q]) :
    (((algebraMap ℤ_[q] (Rw q Kw) z : Rw q Kw) : Kw) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) z := rfl

scoped instance isScalarTower_int_Rw : IsScalarTower ℤ_[q] (Rw q Kw) Kw :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

scoped instance isLocalHom_algebraMap_Rw : IsLocalHom (algebraMap ℤ_[q] (Rw q Kw)) := by
  refine ⟨fun z hz => ?_⟩
  have h1 := norm_eq_one_of_isUnit q Kw hz
  rw [algebraMap_int_coe, PadicAlgCl.norm_extends] at h1
  exact PadicInt.isUnit_iff.mpr h1

theorem moduleFinite_int_Rw [Module.Finite ℤ_[q] (integralClosure ℤ_[q] Kw)] : Module.Finite ℤ_[q] (Rw q Kw) := by
  let f : integralClosure ℤ_[q] Kw →ₗ[ℤ_[q]] Rw q Kw :=
    { toFun := intClosureEquivRw q Kw
      map_add' := fun x y => map_add _ x y
      map_smul' := fun z x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  exact Module.Finite.of_surjective f (intClosureEquivRw q Kw).surjective

end Ws26T4
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_normalBasis_lattice.Ws26T4"

namespace Ws26HL
open ExtCitation.LocalLevel

variable (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
  (G : Type) [Group G] [MulSemiringAction G L]

noncomputable def actAlgEquiv (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) :
    L ≃ₐ[ℚ_[q]] L :=
  { MulSemiringAction.toRingEquiv G L g with commutes' := hG g }

theorem actAlgEquiv_apply (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (g : G) (x : L) : actAlgEquiv q L G hG g x = g • x := rfl

theorem smul_mem_Rw (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (g : G) {x : L} (hx : x ∈ Rw q L) : g • x ∈ Rw q L := by
  rw [← actAlgEquiv_apply q L G hG]
  exact (ExtCitation.LocalLevel.algEquiv_apply_mem_Rw_iff q L _ x).mpr hx

theorem smul_int_smul (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (g : G) (z : ℤ_[q]) (x : L) : g • (z • x) = z • g • x := by
  rw [← IsScalarTower.algebraMap_smul ℚ_[q] z x, Algebra.smul_def, smul_mul', hG,
    ← IsScalarTower.algebraMap_smul ℚ_[q] z (g • x), Algebra.smul_def]

theorem int_smul_mem_Rw (z : ℤ_[q]) {x : L} (hx : x ∈ Rw q L) : z • x ∈ Rw q L := by
  rw [Ws26T4D.mem_Rw_iff_norm_le_one] at hx ⊢
  rw [← IsScalarTower.algebraMap_smul ℚ_[q] z x, IntermediateField.coe_smul, Algebra.smul_def, norm_mul,
    PadicAlgCl.norm_extends]
  exact mul_le_one₀ (PadicInt.norm_le_one z) (norm_nonneg _) hx

noncomputable def fixedInt (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    Submodule ℤ_[q] L where
  carrier := {x | (∀ g : G, g • x = x) ∧ x ∈ Rw q L}
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨fun g => by rw [smul_add, hx1, hy1], add_mem hx2 hy2⟩
  zero_mem' := ⟨fun g => smul_zero g, (Rw q L).zero_mem⟩
  smul_mem' := by
    rintro z x ⟨hx1, hx2⟩
    exact ⟨fun g => by rw [smul_int_smul q L G hG, hx1], int_smul_mem_Rw q L z hx2⟩

theorem mem_fixedInt (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (x : L) :
    x ∈ fixedInt q L G hG ↔ (∀ g : G, g • x = x) ∧ x ∈ Rw q L := Iff.rfl

end Ws26HL
p2m_reactivate "P2MW.S_ExtCitation_LocalLevel_exists_normalBasis_lattice.Ws26T4"

open Ws26HL Ws26T4 Ws26T4D ExtCitation.LocalLevel in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
    ∃ (A₀ A : Submodule ℤ_[q] L) (c : ℕ),
      A.FG ∧
      (∀ a ∈ A, a ∈ Rw q L) ∧
      (∀ (g : G) (a : L), a ∈ A → g • a ∈ A) ∧
      (∀ x : G → L, (∀ g, x g ∈ A₀) → (∑ᶠ g, g • x g) ∈ A) ∧
      (∀ a ∈ A, ∃! x : G → L, (∀ g, x g ∈ A₀) ∧ (∑ᶠ g, g • x g) = a) ∧
      (∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hq0 : (q : L) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqpos : ∀ n : ℕ, (0 : ℝ) < (q : ℝ) ^ n := fun n => pow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) n
  set K₀ := FixedPoints.subfield G L with hK₀
  have hmemK₀ : ∀ x : L, x ∈ K₀ ↔ ∀ g : G, g • x = x := fun _ => Iff.rfl
  let eG : G ≃* (L ≃ₐ[K₀] L) := FixedPoints.toAlgAutMulEquiv G L
  let nb := IsGalois.normalBasis K₀ L
  set θ₀ : L := nb 1 with hθ₀

  have hqfix : ∀ (g : G) (n : ℕ), g • ((q : L) ^ n) = (q : L) ^ n := fun g n => by
    rw [smul_pow', ← map_natCast (algebraMap ℚ_[q] L), hG]
  have hnorm_qpow : ∀ (n : ℕ) (y : L),
      ‖(((q : L) ^ n * y : L) : PadicAlgCl q)‖ = ((q : ℝ) ^ n)⁻¹ * ‖(y : PadicAlgCl q)‖ := by
    intro n y
    push_cast
    rw [norm_mul, norm_pow, ← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)), PadicAlgCl.norm_extends,
      Padic.norm_p, inv_pow]
  have hscale_mono : ∀ (y : L) (n n' : ℕ), n ≤ n' → (q : L) ^ n * y ∈ Rw q L → (q : L) ^ n' * y ∈ Rw q L := by
    intro y n n' hle h
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    rw [pow_add, mul_comm ((q : L) ^ n), mul_assoc]
    have : ((q : L) ^ d) = algebraMap ℤ_[q] L ((q : ℤ_[q]) ^ d) := by rw [map_pow, map_natCast]
    rw [this, ← Algebra.smul_def]
    exact int_smul_mem_Rw q L _ h
  have hscale : ∀ y : L, ∃ n : ℕ, ∀ n', n ≤ n' → (q : L) ^ n' * y ∈ Rw q L := by
    intro y
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖(y : PadicAlgCl q)‖
      (by exact_mod_cast (Fact.out : q.Prime).one_lt : (1 : ℝ) < q)
    refine ⟨n, fun n' hn' => hscale_mono y n n' hn' ((mem_Rw_iff_norm_le_one q L _).mpr ?_)⟩
    rw [hnorm_qpow, inv_mul_le_iff₀ (hqpos n), mul_one]
    exact hn.le

  obtain ⟨m, hm⟩ := hscale θ₀
  have hθR : (q : L) ^ m * θ₀ ∈ Rw q L := hm m le_rfl
  set θ : L := (q : L) ^ m * θ₀ with hθ
  have hθ0 : θ ≠ 0 := mul_ne_zero (pow_ne_zero _ hq0) (by rw [hθ₀]; exact nb.ne_zero 1)

  let bG : Module.Basis G K₀ L := nb.reindex eG.toEquiv.symm
  have hbG : ∀ g : G, bG g = g • θ₀ := fun g => by
    simp only [bG, Module.Basis.reindex_apply, Equiv.symm_symm]
    rw [show eG.toEquiv g = eG g from rfl, IsGalois.normalBasis_apply]; rfl
  have hqK : (q : L) ^ m ∈ K₀ := (hmemK₀ _).mpr fun g => hqfix g m
  have hqK0 : (⟨(q : L) ^ m, hqK⟩ : K₀) ≠ 0 := fun h => pow_ne_zero m hq0 (congrArg Subtype.val h)
  let bθ : Module.Basis G K₀ L := bG.unitsSMul fun _ => Units.mk0 _ hqK0
  have hKsmul : ∀ (k : K₀) (x : L), k • x = (k : L) * x := fun _ _ => rfl
  have hbθ : ∀ g : G, bθ g = g • θ := fun g => by
    rw [Module.Basis.unitsSMul_apply, Units.smul_mk0, hbG, hKsmul, hθ, smul_mul', hqfix]
  have hfixK : ∀ (g : G) (k : K₀), g • (k : L) = k := fun g k => (hmemK₀ _).mp k.2 g

  let O : Submodule ℤ_[q] L := fixedInt q L G hG
  have hO : ∀ x : L, x ∈ O ↔ (∀ g : G, g • x = x) ∧ x ∈ Rw q L := fun _ => Iff.rfl
  let Φ : (G → L) →ₗ[ℤ_[q]] L :=
    { toFun := fun c => ∑ g, c g * g • θ
      map_add' := fun c d => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun z c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_mul_assoc] }
  have hΦ : ∀ c : G → L, Φ c = ∑ g, c g * g • θ := fun _ => rfl
  let A : Submodule ℤ_[q] L := Submodule.map Φ (Submodule.pi Set.univ fun _ => O)
  have hmemA : ∀ a : L, a ∈ A ↔ ∃ c : G → L, (∀ g, c g ∈ O) ∧ ∑ g, c g * g • θ = a := by
    intro a
    simp only [A, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ, true_implies, hΦ]
  let A₀ : Submodule ℤ_[q] L := Submodule.map (LinearMap.mulRight ℤ_[q] θ) O
  have hmemA₀ : ∀ x : L, x ∈ A₀ ↔ ∃ o ∈ O, o * θ = x := by
    intro x; simp only [A₀, Submodule.mem_map, LinearMap.mulRight_apply]

  have hsum_repr : ∀ y : L, ∑ g, (bθ.repr y g : L) * g • θ = y := by
    intro y
    conv_rhs => rw [← bθ.sum_repr y]
    exact Finset.sum_congr rfl fun g _ => by rw [hKsmul, hbθ]
  have hrepr : ∀ (c : G → L) (hc : ∀ g, c g ∈ K₀) (g : G),
      (bθ.repr (∑ h, c h * h • θ) g : L) = c g := by
    intro c hc g
    have : ∑ h, c h * h • θ = ∑ h, (⟨c h, hc h⟩ : K₀) • bθ h :=
      Finset.sum_congr rfl fun h _ => by rw [hKsmul, hbθ]
    rw [this, ← bθ.equivFun_symm_apply, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hsmul_oθ : ∀ (g : G) (o : L), (∀ h : G, h • o = o) → g • (o * θ) = o * g • θ := by
    intro g o ho; rw [smul_mul', ho]

  have hone : ∀ y : L, ∃ n : ℕ, (q : L) ^ n * y ∈ A := by
    intro y
    choose ny hny using fun g => hscale (bθ.repr y g : L)
    refine ⟨Finset.univ.sup ny, (hmemA _).mpr ⟨fun g => (q : L) ^ (Finset.univ.sup ny) * (bθ.repr y g : L),
      fun g => (hO _).mpr ⟨fun h => by rw [smul_mul', hqfix, hfixK], hny g _ (Finset.le_sup (Finset.mem_univ g))⟩, ?_⟩⟩
    calc ∑ g, (q : L) ^ (Finset.univ.sup ny) * (bθ.repr y g : L) * g • θ
        = (q : L) ^ (Finset.univ.sup ny) * ∑ g, (bθ.repr y g : L) * g • θ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun g _ => by rw [mul_assoc]
      _ = (q : L) ^ (Finset.univ.sup ny) * y := by rw [hsum_repr]

  have hfull : ∃ c : ℕ, ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A := by
    obtain ⟨hfinL, hdvrL, -⟩ :=
      integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal ℤ_[q] ℚ_[q] L
    haveI := hdvrL
    haveI := hfinL
    letI : Algebra ℤ_[q] (Rw q L) := algInt q L
    haveI : Module.Finite ℤ_[q] (Rw q L) := moduleFinite_int_Rw q L
    obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ_[q]) (M := Rw q L)
    choose n hn using hone
    refine ⟨S.sup fun s => n (s : L), fun y hy => ?_⟩
    set c := S.sup fun s => n (s : L) with hc
    have hqsmul : ∀ (k : ℕ) (z : L), ((q : ℚ_[q]) ^ k) • z = (q : L) ^ k * z := fun k z => by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [hqsmul]

    have hgen : ∀ s ∈ S, (q : L) ^ c * ((s : Rw q L) : L) ∈ A := by
      intro s hs
      have hle : n ((s : Rw q L) : L) ≤ c := Finset.le_sup (f := fun s : Rw q L => n (s : L)) hs
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hle
      rw [hd, pow_add, mul_comm ((q : L) ^ n (s : L)), mul_assoc]
      have : ((q : L) ^ d) = algebraMap ℤ_[q] L ((q : ℤ_[q]) ^ d) := by rw [map_pow, map_natCast]
      rw [this, ← Algebra.smul_def]
      exact A.smul_mem _ (hn _)

    have hsmulRw : ∀ (z : ℤ_[q]) (w : Rw q L), ((z • w : Rw q L) : L) = z • (w : L) := fun z w => by
      rw [Algebra.smul_def, Algebra.smul_def]; push_cast; congr 1
    let j : Rw q L →ₗ[ℤ_[q]] L :=
      { toFun := fun w => (w : L), map_add' := fun _ _ => rfl,
        map_smul' := fun z w => by rw [RingHom.id_apply]; exact hsmulRw z w }
    let P : Submodule ℤ_[q] L := A.comap (LinearMap.mulLeft ℤ_[q] ((q : L) ^ c))
    have hP : ∀ z : L, z ∈ P ↔ (q : L) ^ c * z ∈ A := fun _ => Iff.rfl
    have hx : y ∈ Submodule.map j ⊤ := ⟨⟨y, hy⟩, trivial, rfl⟩
    rw [← hS, Submodule.map_span] at hx
    have hle : Submodule.span ℤ_[q] (j '' (S : Set (Rw q L))) ≤ P := by
      rw [Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      exact (hP _).mpr (hgen s hs)
    exact (hP _).mp (hle hx)
  obtain ⟨c, hc⟩ := hfull

  have hOfg : O.FG := by
    obtain ⟨hfinL, hdvrL, -⟩ :=
      integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal ℤ_[q] ℚ_[q] L
    haveI := hdvrL
    haveI := hfinL
    letI : Algebra ℤ_[q] (Rw q L) := algInt q L
    haveI : Module.Finite ℤ_[q] (Rw q L) := moduleFinite_int_Rw q L
    have hsmulRw : ∀ (z : ℤ_[q]) (w : Rw q L), ((z • w : Rw q L) : L) = z • (w : L) := fun z w => by
      rw [Algebra.smul_def, Algebra.smul_def]; push_cast; congr 1
    let j : Rw q L →ₗ[ℤ_[q]] L :=
      { toFun := fun w => (w : L), map_add' := fun _ _ => rfl,
        map_smul' := fun z w => by rw [RingHom.id_apply]; exact hsmulRw z w }
    let W : Submodule ℤ_[q] L := Submodule.map j ⊤
    have hW : W.FG := Submodule.FG.map j Module.Finite.fg_top
    haveI : IsNoetherian ℤ_[q] W := isNoetherian_of_fg_of_noetherian W hW
    have hOW : O ≤ W := fun x hx => ⟨⟨x, ((hO x).mp hx).2⟩, trivial, rfl⟩
    have h1 : (O.comap W.subtype).FG := IsNoetherian.noetherian _
    have h2 : O = Submodule.map W.subtype (O.comap W.subtype) := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hOW]
    rw [h2]; exact h1.map _
  refine ⟨A₀, A, c, Submodule.FG.map _ (Submodule.fg_pi fun _ => hOfg), ?_, ?_, ?_, ?_, hc⟩
  · intro a ha
    obtain ⟨c, hc, rfl⟩ := (hmemA a).mp ha
    exact sum_mem fun g _ => mul_mem ((hO _).mp (hc g)).2 (smul_mem_Rw q L G hG g hθR)
  · intro h a ha
    obtain ⟨c, hc, rfl⟩ := (hmemA a).mp ha
    refine (hmemA _).mpr ⟨fun g => c (h⁻¹ * g), fun g => hc _, ?_⟩
    rw [Finset.smul_sum]
    symm
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    rw [smul_mul', ((hO _).mp (hc g)).1 h, mul_smul]
  · intro x hx
    rw [finsum_eq_sum_of_fintype]
    choose o ho hox using fun g => (hmemA₀ _).mp (hx g)
    refine (hmemA _).mpr ⟨o, ho, Finset.sum_congr rfl fun g _ => ?_⟩
    rw [← hox g, hsmul_oθ g _ ((hO _).mp (ho g)).1]
  · intro a ha
    obtain ⟨c, hc, rfl⟩ := (hmemA a).mp ha
    have hKc : ∀ g, c g ∈ K₀ := fun g => (hmemK₀ _).mpr ((hO _).mp (hc g)).1
    refine ⟨fun g => c g * θ, ⟨fun g => (hmemA₀ _).mpr ⟨c g, hc g, rfl⟩, ?_⟩, ?_⟩
    · rw [finsum_eq_sum_of_fintype]
      exact Finset.sum_congr rfl fun g _ => hsmul_oθ g _ ((hO _).mp (hc g)).1
    · rintro x ⟨hx, hxa⟩
      funext g
      choose o' ho' hox' using fun g => (hmemA₀ _).mp (hx g)
      have hKo' : ∀ g, o' g ∈ K₀ := fun g => (hmemK₀ _).mpr ((hO _).mp (ho' g)).1
      have hsum : ∑ g, o' g * g • θ = ∑ g, c g * g • θ := by
        rw [← hxa, finsum_eq_sum_of_fintype]
        exact Finset.sum_congr rfl fun g _ => by rw [← hox' g, hsmul_oθ g _ ((hO _).mp (ho' g)).1]
      have h1 := hrepr o' hKo' g
      rw [hsum, hrepr c hKc g] at h1
      rw [← hox' g, h1]

end S_ExtCitation_LocalLevel_exists_normalBasis_lattice
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_normalBasis_lattice (solution)
