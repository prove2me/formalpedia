-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/cfc0710d-8abd-5ca4-bbb4-e27017c90c24

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import Theorems.Thm_ExtCitation_LocalLevel_exists_normalBasis_lattice
import Theorems.Thm_exists_mem_addSubgroup_one_add_mul_one_add_eq_one
import Theorems.Thm_exists_units_forall_div_sub_one_mem
import Theorems.Thm_groupCohomology_isCoboundary1_of_addEquiv_pi
import Theorems.Thm_groupCohomology_isCoboundary2_of_addEquiv_pi
import Theorems.Thm_groupCohomology_isMulCoboundary1_of_filtration
import Theorems.Thm_groupCohomology_isMulCoboundary2_of_filtration
import Theorems.Thm_groupCohomology_exists_div_mem_of_isMulCocycle1_of_presentation
import Theorems.Thm_groupCohomology_exists_div_mem_of_isMulCocycle2_of_presentation
import Theorems.Thm_ExtCitation_LocalLevel_algEquiv_apply_mem_Rw_iff
import Theorems.Thm_ExtCitation_LocalLevel_isDiscreteValuationRing_Rw
import Theorems.Thm_ExtCitation_LocalLevel_exists_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_index_principalUnits_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1600000
open ExtCitation.LocalLevel IsLocalRing groupCohomology
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

namespace Ws26HL
open ExtCitation.LocalLevel Ws26T4D

section Lattice
variable (q : ℕ) [Fact q.Prime] (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
  (A : Submodule ℤ_[q] L) (c N : ℕ)

noncomputable def Mn (n : ℕ) : Submodule ℤ_[q] L :=
  A.map (DistribSMul.toLinearMap ℤ_[q] L ((q : ℤ_[q]) ^ (N + n)))

omit [FiniteDimensional ℚ_[q] L] in
theorem mem_Mn {n : ℕ} {x : L} : x ∈ Mn q L A N n ↔ ∃ a ∈ A, ((q : ℤ_[q]) ^ (N + n)) • a = x := by
  simp only [Mn, Submodule.mem_map]; rfl

omit [FiniteDimensional ℚ_[q] L] in
theorem qsmul_eq (k : ℕ) (x : L) : ((q : ℤ_[q]) ^ k) • x = (q : L) ^ k * x := by
  rw [← IsScalarTower.algebraMap_smul ℚ_[q] ((q : ℤ_[q]) ^ k) x, Algebra.smul_def, map_pow, map_pow,
    map_natCast, map_natCast]

omit [FiniteDimensional ℚ_[q] L] in
theorem Mn_le_Mn {n k : ℕ} (h : n ≤ k) : Mn q L A N k ≤ Mn q L A N n := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := (mem_Mn q L A N).mp hx
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine (mem_Mn q L A N).mpr ⟨((q : ℤ_[q]) ^ d) • a, A.smul_mem _ ha, ?_⟩
  rw [smul_smul, ← pow_add]; congr 2; omega

theorem Mn_antitone : Antitone (Mn q L A N) := fun _ _ h => Mn_le_Mn q L A N h

theorem mul_mem_Mn (hAsub : ∀ a ∈ A, a ∈ Rw q L) (hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A)
    (hN : c + 1 ≤ N) {n k : ℕ} {x y : L} (hx : x ∈ Mn q L A N n) (hy : y ∈ Mn q L A N k) :
    x * y ∈ Mn q L A N (n + k + 1) := by
  obtain ⟨a, ha, rfl⟩ := (mem_Mn q L A N).mp hx
  obtain ⟨b, hb, rfl⟩ := (mem_Mn q L A N).mp hy
  have hab : ((q : ℚ_[q]) ^ c) • (a * b) ∈ A := hAfull _ (mul_mem (hAsub a ha) (hAsub b hb))
  obtain ⟨d, hd⟩ : ∃ d, N = c + 1 + d := Nat.exists_eq_add_of_le hN
  refine (mem_Mn q L A N).mpr ⟨((q : ℤ_[q]) ^ d) • (((q : ℚ_[q]) ^ c) • (a * b)), A.smul_mem _ hab, ?_⟩
  rw [qsmul_eq, qsmul_eq, qsmul_eq, qsmul_eq, Algebra.smul_def, map_pow, map_natCast]
  have : N + (n + k + 1) + d + c = (N + n) + (N + k) := by omega
  calc (q : L) ^ (N + (n + k + 1)) * ((q : L) ^ d * ((q : L) ^ c * (a * b)))
      = (q : L) ^ (N + (n + k + 1) + d + c) * (a * b) := by ring
    _ = (q : L) ^ ((N + n) + (N + k)) * (a * b) := by rw [this]
    _ = (q : L) ^ (N + n) * a * ((q : L) ^ (N + k) * b) := by ring

theorem norm_le_of_mem_Mn (hAsub : ∀ a ∈ A, a ∈ Rw q L) {n : ℕ} {x : L} (hx : x ∈ Mn q L A N n) :
    ‖(x : PadicAlgCl q)‖ ≤ ((q : ℝ) ^ (N + n))⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := (mem_Mn q L A N).mp hx
  rw [qsmul_eq]
  push_cast
  rw [norm_mul, norm_pow, ← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)), PadicAlgCl.norm_extends,
    Padic.norm_p, inv_pow]
  have h1 : ‖((a : L) : PadicAlgCl q)‖ ≤ 1 := (mem_Rw_iff_norm_le_one q L a).mp (hAsub a ha)
  calc ((q : ℝ) ^ (N + n))⁻¹ * ‖((a : L) : PadicAlgCl q)‖ ≤ ((q : ℝ) ^ (N + n))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg q) _))
    _ = _ := mul_one _

theorem norm_lt_one_of_mem_Mn (hAsub : ∀ a ∈ A, a ∈ Rw q L) {n : ℕ} {x : L} (hx : x ∈ Mn q L A N n)
    (hN : 1 ≤ N) : ‖x‖ < 1 := by
  have h := norm_le_of_mem_Mn q L A N hAsub hx
  have hlt : ((q : ℝ) ^ (N + n))⁻¹ < 1 := by
    rw [inv_lt_one₀ (pow_pos (by exact_mod_cast (Fact.out : q.Prime).pos) _)]
    exact one_lt_pow₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt) (by omega)
  exact lt_of_le_of_lt h hlt

theorem Mn_le_Rw (hAsub : ∀ a ∈ A, a ∈ Rw q L) {n : ℕ} {x : L} (hx : x ∈ Mn q L A N n) : x ∈ Rw q L := by
  obtain ⟨a, ha, rfl⟩ := (mem_Mn q L A N).mp hx
  exact int_smul_mem_Rw q L _ (hAsub a ha)

noncomputable def Vn (hAsub : ∀ a ∈ A, a ∈ Rw q L) (hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A)
    (hN : c + 1 ≤ N) (n : ℕ) : Subgroup (↥L)ˣ where
  carrier := {u | ((u : L) - 1 ∈ Mn q L A N n) ∧ (((u⁻¹ : (↥L)ˣ) : L) - 1 ∈ Mn q L A N n)}
  one_mem' := by
    simp only [Set.mem_setOf_eq, Units.val_one, inv_one, sub_self]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  mul_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    have key : ∀ a b : L, a - 1 ∈ Mn q L A N n → b - 1 ∈ Mn q L A N n → a * b - 1 ∈ Mn q L A N n := by
      intro a b ha hb
      have : a * b - 1 = (a - 1) + (b - 1) + (a - 1) * (b - 1) := by ring
      rw [this]
      exact Submodule.add_mem _ (Submodule.add_mem _ ha hb)
        (Mn_le_Mn q L A N (by omega) (mul_mem_Mn q L A c N hAsub hAfull hN ha hb))
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact key _ _ hu1 hv1
    · rw [mul_inv_rev, Units.val_mul]; exact key _ _ hv2 hu2
  inv_mem' := by
    rintro u ⟨hu1, hu2⟩
    exact ⟨hu2, by rw [inv_inv]; exact hu1⟩

variable {q L A c N}

theorem mem_Vn {hAsub : ∀ a ∈ A, a ∈ Rw q L} {hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A}
    {hN : c + 1 ≤ N} {n : ℕ} {u : (↥L)ˣ} :
    u ∈ Vn q L A c N hAsub hAfull hN n ↔ ((u : L) - 1 ∈ Mn q L A N n) ∧ (((u⁻¹ : (↥L)ˣ) : L) - 1 ∈ Mn q L A N n) :=
  Iff.rfl

theorem Vn_antitone {hAsub : ∀ a ∈ A, a ∈ Rw q L} {hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A}
    {hN : c + 1 ≤ N} : Antitone (Vn q L A c N hAsub hAfull hN) := by
  intro n k h u hu
  exact ⟨Mn_le_Mn q L A N h hu.1, Mn_le_Mn q L A N h hu.2⟩

theorem mul_sub_one_sub_mem {hAsub : ∀ a ∈ A, a ∈ Rw q L} {hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A}
    {hN : c + 1 ≤ N} {n : ℕ} {u v : (↥L)ˣ} (hu : u ∈ Vn q L A c N hAsub hAfull hN n)
    (hv : v ∈ Vn q L A c N hAsub hAfull hN n) :
    ((u * v : (↥L)ˣ) : L) - 1 - (((u : L) - 1) + ((v : L) - 1)) ∈ Mn q L A N (n + 1) := by
  have : ((u * v : (↥L)ˣ) : L) - 1 - (((u : L) - 1) + ((v : L) - 1)) = ((u : L) - 1) * ((v : L) - 1) := by
    push_cast; ring
  rw [this]
  exact Mn_le_Mn q L A N (by omega) (mul_mem_Mn q L A c N hAsub hAfull hN hu.1 hv.1)

theorem mem_Vn_succ_of {hAsub : ∀ a ∈ A, a ∈ Rw q L} {hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A}
    {hN : c + 1 ≤ N} {n : ℕ} {u : (↥L)ˣ} (hu : u ∈ Vn q L A c N hAsub hAfull hN n)
    (hu1 : (u : L) - 1 ∈ Mn q L A N (n + 1)) : u ∈ Vn q L A c N hAsub hAfull hN (n + 1) := by
  refine ⟨hu1, ?_⟩
  have hid : ((u⁻¹ : (↥L)ˣ) : L) - 1 = -((u : L) - 1) - (((u⁻¹ : (↥L)ˣ) : L) - 1) * ((u : L) - 1) := by
    have h := u.inv_mul
    push_cast at h ⊢
    linear_combination h
  rw [hid]
  refine Submodule.sub_mem _ (Submodule.neg_mem _ hu1) ?_
  exact Mn_le_Mn q L A N (by omega) (mul_mem_Mn q L A c N hAsub hAfull hN hu.2 hu1)

end Lattice
end Ws26HL

namespace Ws26HL
open ExtCitation.LocalLevel Ws26T4D

section Coord
variable {q : ℕ} [Fact q.Prime] {L : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L]
  {G : Type} [Group G] [Fintype G] [MulSemiringAction G L]
  {A₀ A : Submodule ℤ_[q] L}
  (hAspan : ∀ x : G → L, (∀ g, x g ∈ A₀) → (∑ g, g • x g) ∈ A)
  (hAuniq : ∀ a ∈ A, ∃! x : G → L, (∀ g, x g ∈ A₀) ∧ (∑ g, g • x g) = a)

open Classical in

noncomputable def coord (a : L) : G → L :=
  if h : a ∈ A then (hAuniq a h).exists.choose else 0

theorem coord_mem (a : L) (g : G) : coord hAuniq a g ∈ A₀ := by
  classical
  unfold coord
  split_ifs with h
  · exact (hAuniq a h).exists.choose_spec.1 g
  · exact A₀.zero_mem

theorem sum_coord {a : L} (ha : a ∈ A) : ∑ g, g • coord hAuniq a g = a := by
  classical
  unfold coord
  rw [dif_pos ha]
  exact (hAuniq a ha).exists.choose_spec.2

theorem coord_eq_of {a : L} (ha : a ∈ A) {x : G → L} (hx : ∀ g, x g ∈ A₀) (hxa : ∑ g, g • x g = a) :
    coord hAuniq a = x :=
  (hAuniq a ha).unique ⟨coord_mem hAuniq a, sum_coord hAuniq ha⟩ ⟨hx, hxa⟩

theorem coord_add {a b : L} (ha : a ∈ A) (hb : b ∈ A) :
    coord hAuniq (a + b) = coord hAuniq a + coord hAuniq b := by
  refine coord_eq_of hAuniq (A.add_mem ha hb) (fun g => A₀.add_mem (coord_mem hAuniq a g) (coord_mem hAuniq b g)) ?_
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, sum_coord hAuniq ha, sum_coord hAuniq hb]

theorem coord_int_smul (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (z : ℤ_[q]) {a : L} (ha : a ∈ A) :
    coord hAuniq (z • a) = z • coord hAuniq a := by
  refine coord_eq_of hAuniq (A.smul_mem z ha) (fun g => A₀.smul_mem z (coord_mem hAuniq a g)) ?_
  simp only [Pi.smul_apply, smul_int_smul q L G hG, ← Finset.smul_sum, sum_coord hAuniq ha]

theorem coord_gsmul (hAstab : ∀ (g : G) (a : L), a ∈ A → g • a ∈ A) (h : G) {a : L} (ha : a ∈ A) (g : G) :
    coord hAuniq (h • a) g = coord hAuniq a (h⁻¹ * g) := by
  have := coord_eq_of hAuniq (hAstab h a ha) (x := fun g => coord hAuniq a (h⁻¹ * g))
    (fun g => coord_mem hAuniq a _) ?_
  · rw [this]
  · conv_rhs => rw [← sum_coord hAuniq ha, Finset.smul_sum]
    symm
    refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, mul_smul]

end Coord
end Ws26HL

namespace Ws26HL
open ExtCitation.LocalLevel Ws26T4D

section Topology
variable {q : ℕ} [Fact q.Prime] {L : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L]

theorem continuous_int_smul : Continuous fun p : ℤ_[q] × L => p.1 • p.2 := by
  have : (fun p : ℤ_[q] × L => p.1 • p.2) = fun p => ((p.1 : ℚ_[q])) • p.2 := by
    funext p; exact (IsScalarTower.algebraMap_smul ℚ_[q] p.1 p.2).symm
  rw [this]
  exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd

theorem isCompact_of_fg {A : Submodule ℤ_[q] L} (hA : A.FG) : IsCompact (A : Set L) := by
  classical
  obtain ⟨s, hs⟩ := hA

  let φ : (s → ℤ_[q]) → L := fun c => ∑ i : s, c i • (i : L)
  have hφ : Continuous φ := by
    refine continuous_finset_sum _ fun i _ => ?_
    have heq : (fun c : s → ℤ_[q] => c i • ((i : L))) = (fun p : ℤ_[q] × L => p.1 • p.2) ∘ (fun c => (c i, (i : L))) := rfl
    rw [heq]
    exact continuous_int_smul.comp ((continuous_apply i).prodMk continuous_const)
  have hrange : Set.range φ = (A : Set L) := by
    rw [← hs]
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span i.2)
    · intro hx
      rw [SetLike.mem_coe, Submodule.mem_span_finset] at hx
      obtain ⟨f, -, hf⟩ := hx
      refine ⟨fun i => f i, ?_⟩
      rw [← hf]
      simp only [φ]
      exact (Finset.sum_coe_sort s (fun i => f i • i))
  rw [← hrange]
  exact isCompact_range hφ

theorem isClosed_of_fg {A : Submodule ℤ_[q] L} (hA : A.FG) : IsClosed (A : Set L) :=
  (isCompact_of_fg hA).isClosed

end Topology

section Presentation
variable {q : ℕ} [Fact q.Prime] {L : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L]
  {G : Type} [Group G] [Fintype G] [MulSemiringAction G L]
  {A₀ A : Submodule ℤ_[q] L} {c N : ℕ}
  (hAuniq : ∀ a ∈ A, ∃! x : G → L, (∀ g, x g ∈ A₀) ∧ (∑ g, g • x g) = a)

noncomputable def qA₀ (q : ℕ) [Fact q.Prime] {L : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L]
    (A₀ : Submodule ℤ_[q] L) : Submodule ℤ_[q] ↥A₀ :=
  Submodule.map (DistribSMul.toLinearMap ℤ_[q] ↥A₀ (q : ℤ_[q])) ⊤

theorem mem_qA₀ {y : ↥A₀} : y ∈ qA₀ q A₀ ↔ ∃ z : ↥A₀, (q : ℤ_[q]) • z = y := by
  simp only [qA₀, Submodule.mem_map, Submodule.mem_top, true_and]; rfl

noncomputable def rescale (q : ℕ) [Fact q.Prime] {L : IntermediateField ℚ_[q] (PadicAlgCl q)} (N n : ℕ) (x : L) : L :=
  ((q : L) ^ (N + n))⁻¹ * x

theorem rescale_spec {n : ℕ} {x : L} (hx : x ∈ Mn q L A N n) :
    rescale q N n x ∈ A ∧ ((q : ℤ_[q]) ^ (N + n)) • rescale q N n x = x := by
  obtain ⟨a, ha, rfl⟩ := (mem_Mn q L A N).mp hx
  have hq : ((q : L) ^ (N + n)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
  have h1 : rescale q N n (((q : ℤ_[q]) ^ (N + n)) • a) = a := by
    rw [rescale, qsmul_eq, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  rw [h1]; exact ⟨ha, rfl⟩

noncomputable def present (n : ℕ) (u : (↥L)ˣ) : G → (↥A₀ ⧸ qA₀ q A₀) :=
  fun g => Submodule.Quotient.mk ⟨coord hAuniq (rescale q N n ((u : L) - 1)) g, coord_mem hAuniq _ g⟩

end Presentation
end Ws26HL

namespace Ws26HL
open ExtCitation.LocalLevel Ws26T4D

section PresentationProps
variable {q : ℕ} [Fact q.Prime] {L : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L]
  {G : Type} [Group G] [Fintype G] [MulSemiringAction G L]
  {A₀ A : Submodule ℤ_[q] L} {c N : ℕ}
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (hAsub : ∀ a ∈ A, a ∈ Rw q L) (hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A)
  (hN : c + 1 ≤ N)
  (hAstab : ∀ (g : G) (a : L), a ∈ A → g • a ∈ A)
  (hAspan : ∀ x : G → L, (∀ g, x g ∈ A₀) → (∑ g, g • x g) ∈ A)
  (hAuniq : ∀ a ∈ A, ∃! x : G → L, (∀ g, x g ∈ A₀) ∧ (∑ g, g • x g) = a)

omit [FiniteDimensional ℚ_[q] L] in
theorem rescale_add (n : ℕ) (x y : L) : rescale q N n (x + y) = rescale q N n x + rescale q N n y := by
  simp only [rescale, mul_add]

omit [FiniteDimensional ℚ_[q] L] in
theorem rescale_succ (n : ℕ) (x : L) : rescale q N n x = (q : ℤ_[q]) • rescale q N (n + 1) x := by
  have hq : (q : L) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have h1 : ∀ y : L, (q : ℤ_[q]) • y = (q : L) * y := fun y => by
    rw [← pow_one (q : ℤ_[q]), qsmul_eq, pow_one]
  rw [rescale, rescale, h1, show N + (n + 1) = (N + n) + 1 by omega, pow_succ]
  field_simp

omit [FiniteDimensional ℚ_[q] L] in
theorem rescale_qsmul (n : ℕ) (a : L) : rescale q N n (((q : ℤ_[q]) ^ (N + n)) • a) = a := by
  have hq : ((q : L) ^ (N + n)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
  rw [rescale, qsmul_eq, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

include hG in
omit [FiniteDimensional ℚ_[q] L] in
theorem rescale_gsmul (n : ℕ) (g : G) (x : L) : rescale q N n (g • x) = g • rescale q N n x := by
  rw [rescale, rescale, smul_mul', smul_inv'', smul_pow', ← map_natCast (algebraMap ℚ_[q] L), hG]

include hG in

theorem present_coord_eq_zero {n : ℕ} {x : L} (hx : x ∈ Mn q L A N (n + 1)) (g : G) :
    (Submodule.Quotient.mk ⟨coord hAuniq (rescale q N n x) g, coord_mem hAuniq _ g⟩ : ↥A₀ ⧸ qA₀ q A₀) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, mem_qA₀]
  have hr : rescale q N (n + 1) x ∈ A := (rescale_spec hx).1
  refine ⟨⟨coord hAuniq (rescale q N (n + 1) x) g, coord_mem hAuniq _ g⟩, Subtype.ext ?_⟩
  show (q : ℤ_[q]) • coord hAuniq (rescale q N (n + 1) x) g = coord hAuniq (rescale q N n x) g
  rw [rescale_succ n x, coord_int_smul hAuniq hG _ hr, Pi.smul_apply]

include hG in
theorem present_mul {n : ℕ} {u v : (↥L)ˣ} (hu : u ∈ Vn q L A c N hAsub hAfull hN n)
    (hv : v ∈ Vn q L A c N hAsub hAfull hN n) :
    present (N := N) hAuniq n (u * v) = present (N := N) hAuniq n u + present (N := N) hAuniq n v := by
  funext g
  set d : L := ((u * v : (↥L)ˣ) : L) - 1 - (((u : L) - 1) + ((v : L) - 1)) with hd
  have hdM : d ∈ Mn q L A N (n + 1) := mul_sub_one_sub_mem hu hv
  have hsplit : ((u * v : (↥L)ˣ) : L) - 1 = (((u : L) - 1) + ((v : L) - 1)) + d := by rw [hd]; ring
  have hru : rescale q N n ((u : L) - 1) ∈ A := (rescale_spec hu.1).1
  have hrv : rescale q N n ((v : L) - 1) ∈ A := (rescale_spec hv.1).1
  have hrd : rescale q N n d ∈ A := (rescale_spec (Mn_le_Mn q L A N (Nat.le_succ n) hdM)).1
  simp only [present, Pi.add_apply]
  have hzero := present_coord_eq_zero hG hAuniq hdM g
  have hcoordsum : coord hAuniq (rescale q N n (((u * v : (↥L)ˣ) : L) - 1)) =
      coord hAuniq (rescale q N n ((u : L) - 1)) + coord hAuniq (rescale q N n ((v : L) - 1)) +
        coord hAuniq (rescale q N n d) := by
    rw [hsplit, rescale_add, rescale_add, coord_add hAuniq (A.add_mem hru hrv) hrd, coord_add hAuniq hru hrv]
  have helem : (⟨coord hAuniq (rescale q N n (((u * v : (↥L)ˣ) : L) - 1)) g, coord_mem hAuniq _ g⟩ : ↥A₀)
      = ⟨coord hAuniq (rescale q N n ((u : L) - 1)) g, coord_mem hAuniq _ g⟩
        + ⟨coord hAuniq (rescale q N n ((v : L) - 1)) g, coord_mem hAuniq _ g⟩
        + ⟨coord hAuniq (rescale q N n d) g, coord_mem hAuniq _ g⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_add]
    rw [hcoordsum]; rfl
  rw [helem, Submodule.Quotient.mk_add, Submodule.Quotient.mk_add, hzero, add_zero]

include hG hAspan in
theorem present_eq_zero_iff {n : ℕ} {u : (↥L)ˣ} (hu : u ∈ Vn q L A c N hAsub hAfull hN n) :
    present (N := N) hAuniq n u = 0 ↔ u ∈ Vn q L A c N hAsub hAfull hN (n + 1) := by
  constructor
  · intro h
    refine mem_Vn_succ_of hu ?_

    have hr : rescale q N n ((u : L) - 1) ∈ A := (rescale_spec hu.1).1
    have hcoord : ∀ g, ∃ z : ↥A₀, (q : ℤ_[q]) • (z : L) = coord hAuniq (rescale q N n ((u : L) - 1)) g := by
      intro g
      have hg := congrFun h g
      simp only [present, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, mem_qA₀] at hg
      obtain ⟨z, hz⟩ := hg
      exact ⟨z, by rw [← Submodule.coe_smul, hz]⟩
    choose z hz using hcoord
    have hsum : rescale q N n ((u : L) - 1) = (q : ℤ_[q]) • ∑ g, g • (z g : L) := by
      rw [← sum_coord hAuniq hr, Finset.smul_sum]
      exact Finset.sum_congr rfl fun g _ => by rw [← hz g, smul_int_smul q L G hG]
    have hA' : ∑ g, g • (z g : L) ∈ A := hAspan _ fun g => (z g).2

    have := (rescale_spec hu.1).2
    rw [← this, hsum, smul_smul, ← pow_succ]
    exact (mem_Mn q L A N).mpr ⟨_, hA', rfl⟩
  · intro h
    funext g
    simp only [present, Pi.zero_apply]
    exact present_coord_eq_zero hG hAuniq h.1 g

end PresentationProps
end Ws26HL

namespace Ws26HL
open ExtCitation.LocalLevel Ws26T4D

section PresentationProps2
variable {q : ℕ} [Fact q.Prime] {L : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L]
  {G : Type} [Group G] [Fintype G] [MulSemiringAction G L]
  {A₀ A : Submodule ℤ_[q] L} {c N : ℕ}
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (hAfg : A.FG)
  (hAsub : ∀ a ∈ A, a ∈ Rw q L) (hAfull : ∀ y : L, y ∈ Rw q L → ((q : ℚ_[q]) ^ c) • y ∈ A)
  (hN : c + 1 ≤ N)
  (hAstab : ∀ (g : G) (a : L), a ∈ A → g • a ∈ A)
  (hAspan : ∀ x : G → L, (∀ g, x g ∈ A₀) → (∑ g, g • x g) ∈ A)
  (hAuniq : ∀ a ∈ A, ∃! x : G → L, (∀ g, x g ∈ A₀) ∧ (∑ g, g • x g) = a)

include hAfg in
theorem isClosed_Mn (n : ℕ) : IsClosed (Mn q L A N n : Set L) := isClosed_of_fg (hAfg.map _)

include hAfg in

theorem exists_unit_one_add [CompleteSpace L] {n : ℕ} {x : L} (hx : x ∈ Mn q L A N n) :
    ∃ u : (↥L)ˣ, (u : L) = 1 + x ∧ u ∈ Vn q L A c N hAsub hAfull hN n := by
  obtain ⟨y, hy, hxy⟩ := exists_mem_addSubgroup_one_add_mul_one_add_eq_one (Mn q L A N n).toAddSubgroup
    (isClosed_Mn hAfg n)
    (fun a b ha hb => Mn_le_Mn q L A N (by omega) (mul_mem_Mn q L A c N hAsub hAfull hN ha hb))
    (fun a ha => norm_lt_one_of_mem_Mn q L A N hAsub ha (by omega)) hx
  refine ⟨⟨1 + x, 1 + y, hxy, by rw [mul_comm]; exact hxy⟩, rfl, ?_, ?_⟩
  · show (1 + x : L) - 1 ∈ _; rw [add_sub_cancel_left]; exact hx
  · show (1 + y : L) - 1 ∈ _; rw [add_sub_cancel_left]; exact hy

include hAfg hAspan in
theorem present_surjective [CompleteSpace L] (n : ℕ) (p : G → (↥A₀ ⧸ qA₀ q A₀)) :
    ∃ u ∈ Vn q L A c N hAsub hAfull hN n, present (N := N) hAuniq n u = p := by
  choose z hz using fun g => Submodule.Quotient.mk_surjective (qA₀ q A₀) (p g)
  set a : L := ∑ g, g • (z g : L) with ha
  have haA : a ∈ A := hAspan _ fun g => (z g).2
  have hx : ((q : ℤ_[q]) ^ (N + n)) • a ∈ Mn q L A N n := (mem_Mn q L A N).mpr ⟨a, haA, rfl⟩
  obtain ⟨u, hu, huV⟩ := exists_unit_one_add hAfg hAsub hAfull hN hx
  refine ⟨u, huV, funext fun g => ?_⟩
  rw [← hz g]
  simp only [present]
  congr 1
  apply Subtype.ext
  show coord hAuniq (rescale q N n ((u : L) - 1)) g = (z g : L)
  rw [hu, add_sub_cancel_left, rescale_qsmul, coord_eq_of hAuniq haA (fun g => (z g).2) ha.symm]

include hG hAstab in
theorem present_gsmul [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    {n : ℕ} {u : (↥L)ˣ} (hu : u ∈ Vn q L A c N hAsub hAfull hN n) (g k : G) :
    present (N := N) hAuniq n (g • u) k = present (N := N) hAuniq n u (g⁻¹ * k) := by
  have hr : rescale q N n ((u : L) - 1) ∈ A := (rescale_spec hu.1).1
  simp only [present]
  congr 1
  apply Subtype.ext
  show coord hAuniq (rescale q N n (((g • u : (↥L)ˣ) : L) - 1)) k = coord hAuniq (rescale q N n ((u : L) - 1)) (g⁻¹ * k)
  rw [hcompat, show g • (u : L) - 1 = g • ((u : L) - 1) by rw [smul_sub, smul_one], rescale_gsmul hG,
    coord_gsmul hAuniq hAstab g hr]

include hG hAstab in

theorem smul_mem_Vn [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    {n : ℕ} (g : G) {u : (↥L)ˣ} (hu : u ∈ Vn q L A c N hAsub hAfull hN n) :
    g • u ∈ Vn q L A c N hAsub hAfull hN n := by
  have key : ∀ w : (↥L)ˣ, (w : L) - 1 ∈ Mn q L A N n → ((g • w : (↥L)ˣ) : L) - 1 ∈ Mn q L A N n := by
    intro w hw
    obtain ⟨a, ha, hwa⟩ := (mem_Mn q L A N).mp hw
    rw [hcompat, show g • (w : L) - 1 = g • ((w : L) - 1) by rw [smul_sub, smul_one], ← hwa,
      smul_int_smul q L G hG]
    exact (mem_Mn q L A N).mpr ⟨g • a, hAstab g a ha, rfl⟩
  refine ⟨key u hu.1, ?_⟩
  rw [← smul_inv']
  exact key _ hu.2

end PresentationProps2
end Ws26HL

namespace Ws26HL

@[reducible] def piSMul (G P : Type*) [Group G] : SMul G (G → P) := ⟨fun h φ k => φ (h⁻¹ * k)⟩
end Ws26HL

set_option maxHeartbeats 0 in
open Ws26HL Ws26T4D ExtCitation.LocalLevel IsLocalRing groupCohomology in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ] (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) :
    ∃ U V : Subgroup (↥L)ˣ,
      (∀ u : (↥L)ˣ, u ∈ U ↔ ((u : L) ∈ Rw q L ∧ ((u⁻¹ : (↥L)ˣ) : L) ∈ Rw q L)) ∧
      (∀ g : G, ∀ u ∈ U, g • u ∈ U) ∧ V ≤ U ∧ (∀ g : G, ∀ v ∈ V, g • v ∈ V) ∧ (V.subgroupOf U).FiniteIndex ∧
      (∃ n : ℕ, 1 ≤ n ∧ ∀ u : (Rw q L)ˣ, u ∈ principalUnits (Rw q L) n →
          Units.map ((Rw q L).subtype : Rw q L →* L) u ∈ V) ∧
      (∀ f : G → (↥L)ˣ, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g) ∧
      (∀ f : G × G → (↥L)ˣ, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
          ∃ x : G → (↥L)ˣ, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : CompleteSpace L := FiniteDimensional.complete ℚ_[q] L
  have hq0 : (q : L) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (Fact.out : q.Prime).pos

  obtain ⟨A₀, A, c, hAfg, hAsub, hAstab, hAspan', hAuniq', hAfull⟩ := exists_normalBasis_lattice q L G hG
  have hAspan : ∀ x : G → L, (∀ g, x g ∈ A₀) → (∑ g, g • x g) ∈ A := fun x hx => by
    rw [← finsum_eq_sum_of_fintype]; exact hAspan' x hx
  have hAuniq : ∀ a ∈ A, ∃! x : G → L, (∀ g, x g ∈ A₀) ∧ (∑ g, g • x g) = a := fun a ha => by
    simpa only [finsum_eq_sum_of_fintype] using hAuniq' a ha
  have hN : c + 1 ≤ c + 1 := le_rfl
  set N := c + 1 with hNdef
  let V : ℕ → Subgroup (↥L)ˣ := Vn q L A c N hAsub hAfull hN
  have hV : ∀ (n : ℕ) (u : (↥L)ˣ), u ∈ V n ↔ ((u : L) - 1 ∈ Mn q L A N n) ∧ (((u⁻¹ : (↥L)ˣ) : L) - 1 ∈ Mn q L A N n) :=
    fun _ _ => Iff.rfl

  let U : Subgroup (↥L)ˣ :=
    { carrier := {u | (u : L) ∈ Rw q L ∧ ((u⁻¹ : (↥L)ˣ) : L) ∈ Rw q L}
      one_mem' := by
        refine ⟨?_, ?_⟩ <;> simp only [Units.val_one, inv_one] <;> exact one_mem _
      mul_mem' := by
        rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
        refine ⟨?_, ?_⟩
        · rw [Units.val_mul]; exact mul_mem hu1 hv1
        · rw [mul_inv_rev, Units.val_mul]; exact mul_mem hv2 hu2
      inv_mem' := by
        rintro u ⟨hu1, hu2⟩
        exact ⟨hu2, by rw [inv_inv]; exact hu1⟩ }
  have hU : ∀ u : (↥L)ˣ, u ∈ U ↔ ((u : L) ∈ Rw q L ∧ ((u⁻¹ : (↥L)ˣ) : L) ∈ Rw q L) := fun _ => Iff.rfl
  have hVU : V 0 ≤ U := by
    intro u hu
    have h1 : (u : L) = 1 + ((u : L) - 1) := by ring
    have h2 : ((u⁻¹ : (↥L)ˣ) : L) = 1 + (((u⁻¹ : (↥L)ˣ) : L) - 1) := by ring
    refine ⟨?_, ?_⟩
    · rw [h1]; exact add_mem (one_mem _) (Mn_le_Rw q L A N hAsub hu.1)
    · rw [h2]; exact add_mem (one_mem _) (Mn_le_Rw q L A N hAsub hu.2)

  haveI : IsDiscreteValuationRing (Rw q L) := ExtCitation.LocalLevel.isDiscreteValuationRing_Rw q L
  obtain ⟨e, f, he, -, hspan, -, -⟩ := ExtCitation.LocalLevel.exists_ramification_inertia_Rw q L
  set n₀ : ℕ := e * (N + c) with hn₀
  have hn₀pos : 1 ≤ n₀ := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he.ne' (by omega))
  let Φ : (Rw q L)ˣ →* (↥L)ˣ := Units.map ((Rw q L).subtype : Rw q L →* L)
  have hΦ : ∀ w : (Rw q L)ˣ, ((Φ w : (↥L)ˣ) : L) = ((w : Rw q L) : L) := fun _ => rfl
  have hΦinv : ∀ w : (Rw q L)ˣ, (((Φ w)⁻¹ : (↥L)ˣ) : L) = (((w⁻¹ : (Rw q L)ˣ) : Rw q L) : L) := fun w => by
    rw [← map_inv]; rfl
  have hprinc1 : ∀ w : (Rw q L)ˣ, w ∈ principalUnits (Rw q L) n₀ → ((Φ w : (↥L)ˣ) : L) - 1 ∈ Mn q L A N 0 := by
    intro w hw
    rw [mem_principalUnits_iff, hn₀, pow_mul, ← hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hw
    obtain ⟨r, hr⟩ := hw
    have hr' : ((Φ w : (↥L)ˣ) : L) - 1 = (q : L) ^ (N + c) * (r : L) := by
      rw [hΦ]
      have := congrArg (fun t : Rw q L => (t : L)) hr
      push_cast at this
      exact this
    rw [hr', pow_add, mul_assoc]
    have h2 : (q : L) ^ c * (r : L) = ((q : ℚ_[q]) ^ c) • (r : L) := by
      rw [Algebra.smul_def, map_pow, map_natCast]
    rw [h2, ← qsmul_eq q L]
    exact (mem_Mn q L A N).mpr ⟨_, hAfull _ r.2, by rw [add_zero]⟩
  have hprinc : ∀ w : (Rw q L)ˣ, w ∈ principalUnits (Rw q L) n₀ → Φ w ∈ V 0 := by
    intro w hw
    refine ⟨hprinc1 w hw, ?_⟩
    rw [← map_inv]
    exact hprinc1 w⁻¹ (Subgroup.inv_mem _ hw)

  letI actV : MulDistribMulAction G ↥(V 0) :=
    { smul := fun g v => ⟨g • (v : (↥L)ˣ), smul_mem_Vn hG hAsub hAfull hN hAstab hcompat g v.2⟩
      one_smul := fun v => Subtype.ext (one_smul G (v : (↥L)ˣ))
      mul_smul := fun g h v => Subtype.ext (mul_smul g h (v : (↥L)ˣ))
      smul_mul := fun g v w => Subtype.ext (smul_mul' g (v : (↥L)ˣ) (w : (↥L)ˣ))
      smul_one := fun g => Subtype.ext (smul_one g) }
  have hactV : ∀ (g : G) (v : ↥(V 0)), ((g • v : ↥(V 0)) : (↥L)ˣ) = g • (v : (↥L)ˣ) := fun _ _ => rfl

  let F : ℕ → Subgroup ↥(V 0) := fun n => (V n).subgroupOf (V 0)
  have hF : ∀ (n : ℕ) (v : ↥(V 0)), v ∈ F n ↔ (v : (↥L)ˣ) ∈ V n := fun _ _ => Subgroup.mem_subgroupOf
  have hF0 : F 0 = ⊤ := Subgroup.subgroupOf_self (V 0)
  have hFstab : ∀ (n : ℕ) (g : G) (x : ↥(V 0)), x ∈ F n → g • x ∈ F n := fun n g x hx => by
    rw [hF] at hx ⊢; rw [hactV]; exact smul_mem_Vn hG hAsub hAfull hN hAstab hcompat g hx
  have hFsep : ∀ x : ↥(V 0), (∀ n, x ∈ F n) → x = 1 := by
    intro x hx
    have hx1 : ∀ n, ‖((((x : (↥L)ˣ) : L) - 1 : L) : PadicAlgCl q)‖ ≤ ((q : ℝ) ^ (N + n))⁻¹ := fun n =>
      norm_le_of_mem_Mn q L A N hAsub ((hF n x).mp (hx n)).1
    have h0' : ((((x : (↥L)ˣ) : L) - 1 : L) : PadicAlgCl q) = 0 := by
      rw [← norm_eq_zero]
      refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) (norm_nonneg _)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
        (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt) : ((q : ℝ))⁻¹ < 1)
      calc ‖((((x : (↥L)ˣ) : L) - 1 : L) : PadicAlgCl q)‖ ≤ ((q : ℝ) ^ (N + n))⁻¹ := hx1 n
        _ ≤ ((q : ℝ) ^ n)⁻¹ := by
          rw [inv_le_inv₀ (pow_pos hqpos _) (pow_pos hqpos _)]
          exact pow_le_pow_right₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt.le) (by omega)
        _ = ((q : ℝ))⁻¹ ^ n := by rw [inv_pow]
        _ < ε := hn
        _ ≤ 0 + ε := by rw [zero_add]
    have h0 : ((x : (↥L)ˣ) : L) - 1 = 0 := by exact_mod_cast h0'
    apply Subtype.ext; apply Units.ext
    show ((x : (↥L)ˣ) : L) = 1
    exact sub_eq_zero.mp h0
  have hFcomplete : ∀ s : ℕ → ↥(V 0), (∀ n, s (n + 1) / s n ∈ F n) → ∃ x : ↥(V 0), ∀ n, x / s n ∈ F n := by
    intro s hs
    obtain ⟨x, hx⟩ := exists_units_forall_div_sub_one_mem (fun n => (Mn q L A N n).toAddSubgroup)
      (fun n => isClosed_Mn hAfg n) (fun n k h => Mn_le_Mn q L A N h)
      (fun n a b ha hb => Mn_le_Mn q L A N (by omega) (mul_mem_Mn q L A c N hAsub hAfull hN ha hb))
      (fun a ha => norm_lt_one_of_mem_Mn q L A N hAsub ha (by omega))
      (fun ε hε => by
        obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε
          (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt) : ((q : ℝ))⁻¹ < 1)
        refine ⟨n, fun a ha => lt_of_le_of_lt (norm_le_of_mem_Mn q L A N hAsub ha) ?_⟩
        calc ((q : ℝ) ^ (N + n))⁻¹ ≤ ((q : ℝ) ^ n)⁻¹ := by
              rw [inv_le_inv₀ (pow_pos hqpos _) (pow_pos hqpos _)]
              exact pow_le_pow_right₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt.le) (by omega)
          _ = ((q : ℝ))⁻¹ ^ n := by rw [inv_pow]
          _ < ε := hn)
      (fun n => ((s n : ↥(V 0)) : (↥L)ˣ))
      (fun n => by
        have h := (hF n _).mp (hs n)
        refine ⟨h.1, ?_⟩
        have := h.2
        rwa [Subgroup.coe_div, inv_div] at this)
    have hxV : ∀ n, x / ((s n : ↥(V 0)) : (↥L)ˣ) ∈ V n := fun n => ⟨(hx n).1, by rw [inv_div]; exact (hx n).2⟩
    have hx0 : x ∈ V 0 := by
      have : x = x / ((s 0 : ↥(V 0)) : (↥L)ˣ) * ((s 0 : ↥(V 0)) : (↥L)ˣ) := by rw [div_mul_cancel]
      rw [this]; exact (V 0).mul_mem (hxV 0) (s 0).2
    refine ⟨⟨x, hx0⟩, fun n => (hF n _).mpr ?_⟩
    rw [Subgroup.coe_div]; exact hxV n

  letI : SMul G (G → (↥A₀ ⧸ qA₀ q A₀)) := piSMul G _
  have hpiSMul : ∀ (h : G) (p : G → (↥A₀ ⧸ qA₀ q A₀)) (k : G), (h • p) k = p (h⁻¹ * k) := fun _ _ _ => rfl
  let π : ℕ → ↥(V 0) → (G → (↥A₀ ⧸ qA₀ q A₀)) := fun n v => present (N := N) hAuniq n (v : (↥L)ˣ)
  have hπmul : ∀ (n : ℕ) (x y : ↥(V 0)), x ∈ F n → y ∈ F n → π n (x * y) = π n x + π n y := by
    intro n x y hx hy
    exact present_mul hG hAsub hAfull hN hAuniq ((hF n x).mp hx) ((hF n y).mp hy)
  have hπsurj : ∀ (n : ℕ) (p : G → (↥A₀ ⧸ qA₀ q A₀)), ∃ x ∈ F n, π n x = p := by
    intro n p
    obtain ⟨u, hu, hup⟩ := present_surjective hAfg hAsub hAfull hN hAspan hAuniq n p
    exact ⟨⟨u, Vn_antitone (Nat.zero_le n) hu⟩, (hF n _).mpr hu, hup⟩
  have hπker : ∀ (n : ℕ) (x : ↥(V 0)), x ∈ F n → (π n x = 0 ↔ x ∈ F (n + 1)) := by
    intro n x hx
    rw [hF]; exact present_eq_zero_iff hG hAsub hAfull hN hAspan hAuniq ((hF n x).mp hx)
  have hπsmul : ∀ (n : ℕ) (g : G) (x : ↥(V 0)), x ∈ F n → π n (g • x) = g • π n x := by
    intro n g x hx
    funext k
    rw [hpiSMul]
    exact present_gsmul hG hAsub hAfull hN hAstab hAuniq hcompat ((hF n x).mp hx) g k
  have hP1 : ∀ f : G → (G → (↥A₀ ⧸ qA₀ q A₀)), IsCocycle₁ f → IsCoboundary₁ f :=
    groupCohomology.isCoboundary1_of_addEquiv_pi (AddEquiv.refl _) (fun _ _ _ => rfl)
  have hP2 : ∀ f : G × G → (G → (↥A₀ ⧸ qA₀ q A₀)), IsCocycle₂ f → IsCoboundary₂ f :=
    groupCohomology.isCoboundary2_of_addEquiv_pi (AddEquiv.refl _) (fun _ _ _ => rfl)
  have hgr1 : ∀ (n : ℕ) (f : G → ↥(V 0)), (∀ g, f g ∈ F n) → IsMulCocycle₁ f →
      ∃ a ∈ F n, ∀ g, f g / (g • a / a) ∈ F (n + 1) := fun n f hfF hf =>
    groupCohomology.exists_div_mem_of_isMulCocycle1_of_presentation (F n) (F (n + 1)) (hFstab n) (π n)
      (hπmul n) (hπsurj n) (hπker n) (hπsmul n) hP1 f hfF hf
  have hgr2 : ∀ (n : ℕ) (f : G × G → ↥(V 0)), (∀ x, f x ∈ F n) → IsMulCocycle₂ f →
      ∃ c : G → ↥(V 0), (∀ g, c g ∈ F n) ∧ ∀ g h, f (g, h) / (g • c h / c (g * h) * c g) ∈ F (n + 1) :=
    fun n f hfF hf =>
    groupCohomology.exists_div_mem_of_isMulCocycle2_of_presentation (F n) (F (n + 1)) (hFstab n) (π n)
      (hπmul n) (hπsurj n) (hπker n) (hπsmul n) hP2 f hfF hf

  have hfin : ((V 0).subgroupOf U).FiniteIndex := by
    let Φ' : (Rw q L)ˣ →* ↥U := Φ.codRestrict U fun w => ⟨by rw [hΦ]; exact (w : Rw q L).2, by
      rw [hΦinv]; exact ((w⁻¹ : (Rw q L)ˣ) : Rw q L).2⟩
    have hΦ'surj : Function.Surjective Φ' := by
      rintro ⟨u, hu1, hu2⟩
      refine ⟨⟨⟨(u : L), hu1⟩, ⟨((u⁻¹ : (↥L)ˣ) : L), hu2⟩, Subtype.ext (by push_cast; exact mul_inv_cancel₀ u.ne_zero),
        Subtype.ext (by push_cast; exact inv_mul_cancel₀ u.ne_zero)⟩, ?_⟩
      apply Subtype.ext; apply Units.ext; rfl
    have hidx : ((principalUnits (Rw q L) n₀).map Φ').index ≠ 0 := by
      intro h0
      have h1 := Subgroup.index_map_dvd (principalUnits (Rw q L) n₀) hΦ'surj
      rw [h0, zero_dvd_iff] at h1
      exact (ExtCitation.LocalLevel.index_principalUnits_Rw q L hn₀pos).1.index_ne_zero h1
    have hle : (principalUnits (Rw q L) n₀).map Φ' ≤ (V 0).subgroupOf U := by
      rintro _ ⟨w, hw, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact hprinc w hw
    refine ⟨fun h0 => hidx ?_⟩
    have := Subgroup.index_dvd_of_le hle
    rw [h0, zero_dvd_iff] at this
    exact this
  refine ⟨U, V 0, hU, ?_, hVU, ?_, hfin, ⟨n₀, hn₀pos, hprinc⟩, ?_, ?_⟩
  ·
    intro g u hu
    refine ⟨?_, ?_⟩
    · rw [hcompat]; exact smul_mem_Rw q L G hG g hu.1
    · rw [← smul_inv', hcompat]; exact smul_mem_Rw q L G hG g hu.2
  · exact fun g v hv => smul_mem_Vn hG hAsub hAfull hN hAstab hcompat g hv
  ·
    intro f hfV hf
    let f' : G → ↥(V 0) := fun g => ⟨f g, hfV g⟩
    have hf' : IsMulCocycle₁ f' := fun g h => Subtype.ext (by
      show f (g * h) = ((g • f' h * f' g : ↥(V 0)) : (↥L)ˣ)
      rw [Subgroup.coe_mul, hactV]; exact hf g h)
    obtain ⟨x, hx⟩ := groupCohomology.isMulCoboundary1_of_filtration F hF0 hFstab hFcomplete hFsep hgr1 f' hf'
    refine ⟨x, x.2, fun g => ?_⟩
    have := congrArg (fun v : ↥(V 0) => (v : (↥L)ˣ)) (hx g)
    simpa only [Subgroup.coe_div, hactV] using this
  ·
    intro f hfV hf
    let f' : G × G → ↥(V 0) := fun p => ⟨f p, hfV p⟩
    have hf' : IsMulCocycle₂ f' := fun g h j => Subtype.ext (by
      show ((f' (g * h, j) * f' (g, h) : ↥(V 0)) : (↥L)ˣ) = ((g • f' (h, j) * f' (g, h * j) : ↥(V 0)) : (↥L)ˣ)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hactV]; exact hf g h j)
    obtain ⟨x, hx⟩ := groupCohomology.isMulCoboundary2_of_filtration F hF0 hFstab hFcomplete hFsep hgr2 f' hf'
    refine ⟨fun g => x g, fun g => (x g).2, fun g h => ?_⟩
    have := congrArg (fun v : ↥(V 0) => (v : (↥L)ˣ)) (hx g h)
    simpa only [Subgroup.coe_div, Subgroup.coe_mul, hactV] using this

end S_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle (solution)
