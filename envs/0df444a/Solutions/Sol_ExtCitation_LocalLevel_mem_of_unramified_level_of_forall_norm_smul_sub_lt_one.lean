-- Prove2me | solution 1 for ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/acbfe11a-60fb-55e6-97d8-3770b00ca692

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw finite_residueField_Rw"
namespace Ws25IT
p2m_open "ExtCitation.LocalLevel ExtCitation"

open IsLocalRing

section Layer

variable {q : ℕ} [Fact q.Prime]
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L]

noncomputable def autOf (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) :
    L ≃ₐ[ℚ_[q]] L :=
  { MulSemiringAction.toRingEquiv G L g with
    commutes' := fun x => hG g x }

theorem autOf_apply (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) (x : L) :
    autOf hG g x = g • x := rfl

theorem norm_smul_eq (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) (x : L) :
    ‖((g • x : L) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q)‖ := by
  haveI : Normal ℚ_[q] (PadicAlgCl q) := IsAlgClosure.normal ℚ_[q] (PadicAlgCl q)
  have hcomm : (autOf hG g).liftNormal (PadicAlgCl q) (algebraMap L (PadicAlgCl q) x) =
      algebraMap L (PadicAlgCl q) (autOf hG g x) :=
    AlgEquiv.liftNormal_commutes (autOf hG g) (PadicAlgCl q) x
  have h1 : ((g • x : L) : PadicAlgCl q) = (autOf hG g).liftNormal (PadicAlgCl q) (x : PadicAlgCl q) := by
    rw [← autOf_apply hG g x]
    exact hcomm.symm
  rw [h1]
  have := nnnorm_padicAlgCl_algEquiv q ((autOf hG g).liftNormal (PadicAlgCl q)) (x : PadicAlgCl q)
  have := congrArg NNReal.toReal this
  simpa only [coe_nnnorm] using this

theorem norm_smul_sub (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (g : G) (x y : L) :
    ‖((g • x : L) : PadicAlgCl q) - ((g • y : L) : PadicAlgCl q)‖ = ‖(x : PadicAlgCl q) - (y : PadicAlgCl q)‖ := by
  have : ((g • x : L) : PadicAlgCl q) - ((g • y : L) : PadicAlgCl q) = ((g • (x - y) : L) : PadicAlgCl q) := by
    rw [smul_sub]; push_cast; ring
  rw [this, norm_smul_eq hG]
  push_cast; ring_nf

theorem norm_pow_smul_sub_lt_one (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (P : L → Prop)
    (g : G) (hg : ∀ x : L, P x → ‖((g • x : L) : PadicAlgCl q) - (x : PadicAlgCl q)‖ < 1)
    (k : ℕ) (x : L) (hx : P x) : ‖((g ^ k • x : L) : PadicAlgCl q) - (x : PadicAlgCl q)‖ < 1 := by
  induction k with
  | zero => rw [pow_zero, one_smul, sub_self, norm_zero]; exact one_pos
  | succ k ih =>
    have hsplit : ((g ^ (k + 1) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) =
        (((g • (g ^ k • x) : L) : PadicAlgCl q) - ((g • x : L) : PadicAlgCl q)) +
          (((g • x : L) : PadicAlgCl q) - (x : PadicAlgCl q)) := by
      rw [pow_succ', mul_smul]; ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ (hg x hx))
    rw [norm_smul_sub hG]
    exact ih

theorem smulCommClass (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) : SMulCommClass G ℚ_[q] L :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG g c]⟩

theorem smulCommClass_subgroup (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (H : Subgroup G) : SMulCommClass H ℚ_[q] L :=
  ⟨fun h c x => (smulCommClass hG).smul_comm (h : G) c x⟩

noncomputable def fixedLevel (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (H : Subgroup G) : IntermediateField ℚ_[q] (PadicAlgCl q) :=
  letI := smulCommClass_subgroup hG H
  IntermediateField.lift (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) H)

theorem mem_fixedLevel_iff (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (H : Subgroup G) (x : L) :
    (x : PadicAlgCl q) ∈ fixedLevel hG H ↔ ∀ h ∈ H, h • x = x := by
  letI := smulCommClass_subgroup hG H
  unfold fixedLevel
  rw [IntermediateField.mem_lift]
  exact ⟨fun hx h hh => hx ⟨h, hh⟩, fun hx h => hx h h.2⟩

theorem fixedLevel_le (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (H : Subgroup G) : fixedLevel hG H ≤ L := by
  letI := smulCommClass_subgroup hG H
  exact IntermediateField.lift_le _

theorem exists_coe_eq_of_mem_fixedLevel (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) (H : Subgroup G) (z : PadicAlgCl q) (hz : z ∈ fixedLevel hG H) :
    ∃ x : L, (x : PadicAlgCl q) = z ∧ ∀ h ∈ H, h • x = x := by
  refine ⟨⟨z, fixedLevel_le hG H hz⟩, rfl, ?_⟩
  exact (mem_fixedLevel_iff hG H ⟨z, fixedLevel_le hG H hz⟩).mp hz

theorem fixedLevel_mono (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) {H₁ H₂ : Subgroup G} (h : H₁ ≤ H₂) : fixedLevel hG H₂ ≤ fixedLevel hG H₁ := by
  intro z hz
  obtain ⟨x, rfl, hx⟩ := exists_coe_eq_of_mem_fixedLevel hG H₂ z hz
  rw [mem_fixedLevel_iff]
  exact fun k hk => hx k (h hk)

theorem finiteDimensional_fixedLevel (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) [FiniteDimensional ℚ_[q] L] (H : Subgroup G) :
    FiniteDimensional ℚ_[q] (fixedLevel hG H) := by
  letI := smulCommClass_subgroup hG H
  haveI : FiniteDimensional ℚ_[q] (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) H) :=
    IntermediateField.finiteDimensional_left _
  exact LinearEquiv.finiteDimensional
    (IntermediateField.liftAlgEquiv (FixedPoints.intermediateField (F := ℚ_[q]) (E := L) H)).toLinearEquiv

end Layer

end ExtCitation.LocalLevel.Ws25IT

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw finite_residueField_Rw"
namespace Ws25IT
p2m_open "ExtCitation.LocalLevel ExtCitation"
open IsLocalRing

section Integers

variable {q : ℕ} [Fact q.Prime] {Kw : IntermediateField ℚ_[q] (PadicAlgCl q)}

theorem mem_Rw_iff (x : Kw) : x ∈ Rw q Kw ↔ ‖(x : PadicAlgCl q)‖ ≤ 1 := by
  show ‖(x : PadicAlgCl q)‖₊ ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem norm_coe_le_one (x : Rw q Kw) : ‖((x : Kw) : PadicAlgCl q)‖ ≤ 1 := (mem_Rw_iff (x : Kw)).mp x.2

theorem norm_eq_one_of_isUnit {x : Rw q Kw} (hx : IsUnit x) : ‖((x : Kw) : PadicAlgCl q)‖ = 1 := by
  obtain ⟨u, hu⟩ := hx.exists_right_inv
  have hprod : ‖((x : Kw) : PadicAlgCl q)‖ * ‖((u : Kw) : PadicAlgCl q)‖ = 1 := by
    rw [← norm_mul]
    have := congrArg (fun t : Rw q Kw => ((t : Kw) : PadicAlgCl q)) hu
    push_cast at this
    rw [this, norm_one]
  nlinarith [norm_nonneg ((x : Kw) : PadicAlgCl q), norm_nonneg ((u : Kw) : PadicAlgCl q), norm_coe_le_one x,
    norm_coe_le_one u]

theorem isUnit_of_norm_eq_one {x : Rw q Kw} (hx : ‖((x : Kw) : PadicAlgCl q)‖ = 1) : IsUnit x := by
  have hx0 : (x : Kw) ≠ 0 := by
    intro h
    have : ((x : Kw) : PadicAlgCl q) = 0 := by rw [h]; rfl
    rw [this, norm_zero] at hx; exact zero_ne_one hx
  have hinv : (x : Kw)⁻¹ ∈ Rw q Kw := by
    rw [mem_Rw_iff]
    have : (((x : Kw)⁻¹ : Kw) : PadicAlgCl q) = (((x : Kw) : PadicAlgCl q))⁻¹ := by push_cast; rfl
    rw [this, norm_inv, hx, inv_one]
  refine ⟨⟨x, ⟨(x : Kw)⁻¹, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ hx0)
  · exact Subtype.ext (inv_mul_cancel₀ hx0)

theorem mem_maximalIdeal_iff (x : Rw q Kw) : x ∈ maximalIdeal (Rw q Kw) ↔ ‖((x : Kw) : PadicAlgCl q)‖ < 1 := by
  rw [mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · intro h
    exact lt_of_le_of_ne (norm_coe_le_one x) (fun h1 => h (isUnit_of_norm_eq_one h1))
  · intro h hu
    exact absurd (norm_eq_one_of_isUnit hu) h.ne

theorem coe_sub (x y : Rw q Kw) : (((x - y : Rw q Kw) : Kw) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) - ((y : Kw) : PadicAlgCl q) := by
  push_cast; rfl

theorem coe_mul (x y : Rw q Kw) : (((x * y : Rw q Kw) : Kw) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) * ((y : Kw) : PadicAlgCl q) := by
  push_cast; rfl

theorem coe_pow (x : Rw q Kw) (n : ℕ) : (((x ^ n : Rw q Kw) : Kw) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) ^ n := by
  push_cast; rfl

theorem residue_eq_of_norm_sub_lt_one {x y : Rw q Kw}
    (h : ‖((x : Kw) : PadicAlgCl q) - ((y : Kw) : PadicAlgCl q)‖ < 1) : residue (Rw q Kw) x = residue (Rw q Kw) y := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, coe_sub]
  exact h

theorem norm_sub_lt_one_of_residue_eq {x y : Rw q Kw} (h : residue (Rw q Kw) x = residue (Rw q Kw) y) :
    ‖((x : Kw) : PadicAlgCl q) - ((y : Kw) : PadicAlgCl q)‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, coe_sub] at h
  exact h

theorem norm_natCast_q : ‖((q : ℕ) : PadicAlgCl q)‖ = (q : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)), PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_natCast_q_lt_one : ‖((q : ℕ) : PadicAlgCl q)‖ < 1 := by
  rw [norm_natCast_q]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : q.Prime).one_lt)

theorem coe_natCast (n : ℕ) : ((((n : ℕ) : Rw q Kw) : Kw) : PadicAlgCl q) = (n : PadicAlgCl q) := by
  push_cast; rfl

theorem charP_residueField : CharP (ResidueField (Rw q Kw)) q := by
  have h0 : ((q : ℕ) : ResidueField (Rw q Kw)) = 0 := by
    rw [← map_natCast (residue (Rw q Kw)), ← map_zero (residue (Rw q Kw))]
    apply residue_eq_of_norm_sub_lt_one
    rw [coe_natCast, ZeroMemClass.coe_zero, ZeroMemClass.coe_zero, sub_zero]
    exact norm_natCast_q_lt_one
  exact ringChar.of_eq (CharP.ringChar_of_prime_eq_zero (Fact.out : q.Prime) h0)

theorem frobenius_residueField_surjective [Finite (ResidueField (Rw q Kw))] :
    Function.Surjective (fun z : ResidueField (Rw q Kw) => z ^ q) := by
  haveI := charP_residueField (q := q) (Kw := Kw)
  haveI : ExpChar (ResidueField (Rw q Kw)) q := ExpChar.prime (Fact.out : q.Prime)
  have hinj : Function.Injective (frobenius (ResidueField (Rw q Kw)) q) := frobenius_inj _ q
  exact Finite.surjective_of_injective hinj

end Integers
end ExtCitation.LocalLevel.Ws25IT

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw finite_residueField_Rw"
namespace Ws25IT
p2m_open "ExtCitation.LocalLevel ExtCitation"
open IsLocalRing

section Ultra

variable {q : ℕ} [Fact q.Prime]

theorem norm_sub_le_max (a b : PadicAlgCl q) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max a (-b)

theorem norm_sum_lt {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl q) {C : ℝ} (hC : 0 < C)
    (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, norm_zero]; exact hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact h a (Finset.mem_insert_self a s)
    · exact ih (fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem norm_sum_le_one {ι : Type} (s : Finset ι) (f : ι → PadicAlgCl q)
    (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one h

theorem norm_prod_sub_prod_lt_one (n : ℕ) (a b : ℕ → PadicAlgCl q)
    (ha : ∀ i < n, ‖a i‖ ≤ 1) (hb : ∀ i < n, ‖b i‖ ≤ 1) (hab : ∀ i < n, ‖a i - b i‖ < 1) :
    ‖(∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i‖ < 1 := by
  induction n with
  | zero => rw [Finset.prod_range_zero, Finset.prod_range_zero, sub_self, norm_zero]; exact one_pos
  | succ n ih =>
    have ha' : ∀ i < n, ‖a i‖ ≤ 1 := fun i hi => ha i (by omega)
    have hb' : ∀ i < n, ‖b i‖ ≤ 1 := fun i hi => hb i (by omega)
    have hab' : ∀ i < n, ‖a i - b i‖ < 1 := fun i hi => hab i (by omega)
    have hsplit : (∏ i ∈ Finset.range (n + 1), a i) - ∏ i ∈ Finset.range (n + 1), b i =
        (∏ i ∈ Finset.range n, a i) * (a n - b n) + ((∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i) * b n := by
      rw [Finset.prod_range_succ, Finset.prod_range_succ]; ring
    rw [hsplit]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      have h1 : ‖∏ i ∈ Finset.range n, a i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i hi => ha' i (Finset.mem_range.mp hi))
      calc ‖∏ i ∈ Finset.range n, a i‖ * ‖a n - b n‖ ≤ 1 * ‖a n - b n‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hab n (by omega)
    · rw [norm_mul]
      calc ‖(∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i‖ * ‖b n‖
          ≤ ‖(∏ i ∈ Finset.range n, a i) - ∏ i ∈ Finset.range n, b i‖ * 1 :=
            mul_le_mul_of_nonneg_left (hb n (by omega)) (norm_nonneg _)
        _ < 1 := by rw [mul_one]; exact ih ha' hb' hab'

theorem norm_natCast_eq_one {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) : ‖((ℓ : ℕ) : PadicAlgCl q)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[q] (PadicAlgCl q)), PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out : q.Prime) hℓ).mpr (Ne.symm hℓq)

end Ultra

section Fixed

variable {q : ℕ} [Fact q.Prime]
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
variable {G : Type} [Group G] [MulSemiringAction G L]

theorem smul_fixed_of_normal (N : Subgroup G) [N.Normal] {y : L} (hy : ∀ n ∈ N, n • y = y) (k : G) :
    ∀ n ∈ N, n • (k • y) = k • y := by
  intro n hn
  have hconj : k⁻¹ * n * k ∈ N := by
    have := Subgroup.Normal.conj_mem inferInstance n hn k⁻¹
    rwa [inv_inv] at this
  calc n • k • y = k • ((k⁻¹ * n * k) • y) := by rw [← mul_smul, ← mul_smul]; congr 1; group
    _ = k • y := by rw [hy _ hconj]

theorem smul_sum_range_eq (h : G) (ℓ : ℕ) {y : L} (hy : h ^ ℓ • y = y) :
    h • (∑ i ∈ Finset.range ℓ, h ^ i • y) = ∑ i ∈ Finset.range ℓ, h ^ i • y := by
  rw [Finset.smul_sum]
  simp_rw [← mul_smul, ← pow_succ']
  have := Finset.sum_range_succ' (fun i => h ^ i • y) ℓ
  rw [Finset.sum_range_succ, pow_zero, one_smul, hy] at this
  exact (add_right_cancel this).symm

theorem smul_prod_range_eq (h : G) (ℓ : ℕ) {y : L} (hy : h ^ ℓ • y = y) :
    h • (∏ i ∈ Finset.range ℓ, h ^ i • y) = ∏ i ∈ Finset.range ℓ, h ^ i • y := by
  rw [Finset.smul_prod']
  simp_rw [← mul_smul, ← pow_succ']
  have := Finset.prod_range_succ' (fun i => h ^ i • y) ℓ
  rw [Finset.prod_range_succ, pow_zero, one_smul, hy] at this
  by_cases hy0 : y = 0
  · subst hy0
    simp only [smul_zero]
  · exact (mul_right_cancel₀ hy0 this).symm

theorem mem_of_forall_fixed_smul_eq [Finite G] [FaithfulSMul G L] (N : Subgroup G) (h : G)
    (hh : ∀ x : L, (∀ n ∈ N, n • x = x) → h • x = x) : h ∈ N := by
  haveI : FaithfulSMul N L :=
    ⟨fun {n₁ n₂} hn => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) (fun x => hn x))⟩
  have hfix : ∀ x : L, x ∈ FixedPoints.subfield N L → h • x = x :=
    fun x hx => hh x (fun n hn => hx ⟨n, hn⟩)
  obtain ⟨σ, hσ⟩ : ∃ σ : L ≃ₐ[FixedPoints.subfield N L] L, ∀ x : L, σ x = h • x :=
    ⟨{ MulSemiringAction.toRingEquiv G L h with commutes' := fun r => hfix r r.2 }, fun _ => rfl⟩
  obtain ⟨n, hn⟩ := (FixedPoints.toAlgAut_bijective N L).2 σ
  have hnh : (n : G) = h := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := L)
    intro x
    have := AlgEquiv.congr_fun hn x
    rw [MulSemiringAction.toAlgAut_apply, MulSemiringAction.toAlgEquiv_apply, hσ] at this
    exact this
  rw [← hnh]
  exact n.2

end Fixed
end ExtCitation.LocalLevel.Ws25IT

open ExtCitation.LocalLevel.Ws25IT IsLocalRing in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (N : Subgroup G) [N.Normal]
    (π : L) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖)
    (g : G) (hg : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((g • x : L) : PadicAlgCl q) - (x : PadicAlgCl q)‖ < 1) :
    g ∈ N := by
  classical
  by_contra hgN
  have hq : q.Prime := Fact.out

  have hqL : ((q : L) : PadicAlgCl q) = (q : PadicAlgCl q) := by push_cast; rfl
  have hπpos : 0 < ‖(π : PadicAlgCl q)‖ := by
    have hfix : ∀ n ∈ N, n • (q : L) = (q : L) := fun n _ => by
      rw [← map_natCast (algebraMap ℚ_[q] L) q, hG]
    have h1 : ‖((q : L) : PadicAlgCl q)‖ < 1 := by rw [hqL]; exact norm_natCast_q_lt_one
    have h2 := hπmax (q : L) hfix h1
    have h3 : 0 < ‖((q : L) : PadicAlgCl q)‖ := by
      rw [hqL, norm_natCast_q]; exact inv_pos.mpr (by exact_mod_cast hq.pos)
    exact lt_of_lt_of_le h3 h2

  have hm0 : orderOf (QuotientGroup.mk' N g) ≠ 0 := (isOfFinOrder_of_finite _).orderOf_pos.ne'
  have hm1 : orderOf (QuotientGroup.mk' N g) ≠ 1 := fun h1 =>
    hgN ((QuotientGroup.eq_one_iff g).mp (orderOf_eq_one_iff.mp h1))
  obtain ⟨ℓ, hℓ, hℓdvd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ orderOf (QuotientGroup.mk' N g) :=
    ⟨_, Nat.minFac_prime hm1, Nat.minFac_dvd _⟩
  obtain ⟨h, k, hhk, hhord⟩ : ∃ (h : G) (k : ℕ), h = g ^ k ∧ orderOf (QuotientGroup.mk' N h) = ℓ :=
    ⟨_, _, rfl, by rw [map_pow]; exact orderOf_pow_orderOf_div hm0 hℓdvd⟩
  have hhN : h ∉ N := fun hmem => by
    have : orderOf (QuotientGroup.mk' N h) = 1 := orderOf_eq_one_iff.mpr ((QuotientGroup.eq_one_iff h).mpr hmem)
    rw [hhord] at this
    exact hℓ.one_lt.ne' this
  have hhℓ : h ^ ℓ ∈ N := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow, ← hhord, pow_orderOf_eq_one]

  have hres : ∀ (i : ℕ) (x : L), (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((h ^ i • x : L) : PadicAlgCl q) - (x : PadicAlgCl q)‖ < 1 := by
    intro i x hxN hx1
    rw [hhk, ← pow_mul]
    exact norm_pow_smul_sub_lt_one hG (fun x => (∀ n ∈ N, n • x = x) ∧ ‖(x : PadicAlgCl q)‖ ≤ 1) g
      (fun x hx => hg x hx.1 hx.2) (k * i) x ⟨hxN, hx1⟩

  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : Subgroup G, H₀ = N ⊔ Subgroup.zpowers h := ⟨_, rfl⟩
  have hNH : N ≤ H₀ := by rw [hH₀]; exact le_sup_left
  have hhH : h ∈ H₀ := by rw [hH₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers h)
  have hfixH : ∀ x : L, (∀ n ∈ N, n • x = x) → h • x = x → ∀ k ∈ H₀, k • x = x := by
    intro x hxN hxh k hk
    have hle : H₀ ≤ MulAction.stabilizer G x := by
      rw [hH₀]
      exact sup_le (fun n hn => hxN n hn) (Subgroup.zpowers_le.mpr hxh)
    exact hle hk
  obtain ⟨M, hM⟩ : ∃ M : IntermediateField ℚ_[q] (PadicAlgCl q), M = fixedLevel hG N := ⟨_, rfl⟩
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : IntermediateField ℚ_[q] (PadicAlgCl q), M₀ = fixedLevel hG H₀ := ⟨_, rfl⟩
  have hle : M₀ ≤ M := by rw [hM, hM₀]; exact fixedLevel_mono hG hNH
  haveI : FiniteDimensional ℚ_[q] M := by rw [hM]; exact finiteDimensional_fixedLevel hG N
  haveI : FiniteDimensional ℚ_[q] M₀ := by rw [hM₀]; exact finiteDimensional_fixedLevel hG H₀
  have hmemM : ∀ x : L, (x : PadicAlgCl q) ∈ M ↔ ∀ n ∈ N, n • x = x := by
    intro x; rw [hM]; exact mem_fixedLevel_iff hG N x
  have hmemM₀ : ∀ x : L, (x : PadicAlgCl q) ∈ M₀ ↔ ∀ k ∈ H₀, k • x = x := by
    intro x; rw [hM₀]; exact mem_fixedLevel_iff hG H₀ x
  have hofM : ∀ z : PadicAlgCl q, z ∈ M → ∃ x : L, (x : PadicAlgCl q) = z ∧ ∀ n ∈ N, n • x = x := by
    intro z hz; rw [hM] at hz; exact exists_coe_eq_of_mem_fixedLevel hG N z hz

  obtain ⟨e, f, ι, hι, he, hf, hmap, hcard, hfin⟩ :=
    ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw q M₀ M hle

  have hne : M₀ ≠ M := by
    intro hEq
    refine hhN (mem_of_forall_fixed_smul_eq (G := G) (L := L) N h (fun x hx => ?_))
    have hxM : (x : PadicAlgCl q) ∈ M := (hmemM x).mpr hx
    rw [← hEq] at hxM
    exact (hmemM₀ x).mp hxM h hhH
  have hef : e * f ≠ 1 := fun h1 =>
    hne (IntermediateField.eq_of_le_of_finrank_eq hle (by rw [hfin, h1, mul_one]))

  haveI := ExtCitation.LocalLevel.finite_residueField_Rw q M₀
  haveI := ExtCitation.LocalLevel.finite_residueField_Rw q M

  have mk₀ : ∀ t : L, (∀ n ∈ N, n • t = t) → h • t = t → ‖(t : PadicAlgCl q)‖ ≤ 1 →
      ∃ z : Rw q M₀, ((z : M₀) : PadicAlgCl q) = (t : PadicAlgCl q) := by
    intro t htN hth ht1
    exact ⟨⟨⟨(t : PadicAlgCl q), (hmemM₀ t).mpr (hfixH t htN hth)⟩, (mem_Rw_iff _).mpr ht1⟩, rfl⟩

  have hsurj : ∀ X : Rw q M, ∃ z : Rw q M₀, residue (Rw q M) (ι z) = residue (Rw q M) X := by
    intro X
    obtain ⟨y, hyX, hyN⟩ := hofM ((X : M) : PadicAlgCl q) (X : M).2
    have hy1 : ‖(y : PadicAlgCl q)‖ ≤ 1 := by rw [hyX]; exact norm_coe_le_one X
    have hyℓ : h ^ ℓ • y = y := hyN _ hhℓ

    suffices hz : ∃ z : Rw q M₀, ‖((z : M₀) : PadicAlgCl q) - (y : PadicAlgCl q)‖ < 1 by
      obtain ⟨z, hz⟩ := hz
      refine ⟨z, residue_eq_of_norm_sub_lt_one ?_⟩
      rw [hι, ← hyX]
      exact hz
    by_cases hℓq : ℓ = q
    ·
      have hnN : ∀ n ∈ N, n • (∏ i ∈ Finset.range ℓ, h ^ i • y) = ∏ i ∈ Finset.range ℓ, h ^ i • y := by
        intro n hn
        rw [Finset.smul_prod']
        exact Finset.prod_congr rfl (fun i _ => smul_fixed_of_normal N hyN (h ^ i) n hn)
      have hnh : h • (∏ i ∈ Finset.range ℓ, h ^ i • y) = ∏ i ∈ Finset.range ℓ, h ^ i • y :=
        smul_prod_range_eq h ℓ hyℓ
      have hncoe : ((∏ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q) =
          ∏ i ∈ Finset.range ℓ, ((h ^ i • y : L) : PadicAlgCl q) := by push_cast; rfl
      have hn1 : ‖((∏ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q)‖ ≤ 1 := by
        rw [hncoe, norm_prod]
        exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => by rw [norm_smul_eq hG]; exact hy1)
      have hpow : (y : PadicAlgCl q) ^ q = (y : PadicAlgCl q) ^ ℓ := by rw [hℓq]
      have hny : ‖((∏ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q) - (y : PadicAlgCl q) ^ ℓ‖ < 1 := by
        rw [hncoe, show (y : PadicAlgCl q) ^ ℓ = ∏ _i ∈ Finset.range ℓ, (y : PadicAlgCl q) by
          rw [Finset.prod_const, Finset.card_range]]
        exact norm_prod_sub_prod_lt_one ℓ (fun i => ((h ^ i • y : L) : PadicAlgCl q)) (fun _ => (y : PadicAlgCl q))
          (fun i _ => by rw [norm_smul_eq hG]; exact hy1) (fun _ _ => hy1) (fun i _ => hres i y hyN hy1)
      obtain ⟨n₀, hn₀⟩ := mk₀ (∏ i ∈ Finset.range ℓ, h ^ i • y) hnN hnh hn1

      obtain ⟨ω, hω⟩ := frobenius_residueField_surjective (q := q) (Kw := M₀) (residue (Rw q M₀) n₀)
      obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective ω
      have hwq : ‖((w : M₀) : PadicAlgCl q) ^ q - ((n₀ : M₀) : PadicAlgCl q)‖ < 1 := by
        rw [← coe_pow]
        apply norm_sub_lt_one_of_residue_eq
        rw [map_pow]
        exact hω
      refine ⟨w, ?_⟩

      obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hq (ι w - X) X
      rw [sub_add_cancel] at hr
      have hr' : (ι w - X) ^ q = (ι w) ^ q - X ^ q - (q : Rw q M) * (ι w - X) * X * r := by
        rw [hr]; ring
      have hWcoe : (((ι w : Rw q M) : M) : PadicAlgCl q) = ((w : M₀) : PadicAlgCl q) := hι w
      have hXcoe : (((X : Rw q M) : M) : PadicAlgCl q) = (y : PadicAlgCl q) := hyX.symm
      have key := congrArg (fun t : Rw q M => ‖((t : M) : PadicAlgCl q)‖) hr'
      simp only [coe_pow, coe_sub, coe_mul, hWcoe, hXcoe, coe_natCast] at key

      have hA : ‖((w : M₀) : PadicAlgCl q) ^ q - (y : PadicAlgCl q) ^ q‖ < 1 := by
        have : ((w : M₀) : PadicAlgCl q) ^ q - (y : PadicAlgCl q) ^ q =
            (((w : M₀) : PadicAlgCl q) ^ q - ((n₀ : M₀) : PadicAlgCl q)) +
              (((n₀ : M₀) : PadicAlgCl q) - (y : PadicAlgCl q) ^ q) := by ring
        rw [this]
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hwq ?_)
        rw [hn₀, hpow]
        exact hny
      have hB : ‖(q : PadicAlgCl q) * (((w : M₀) : PadicAlgCl q) - (y : PadicAlgCl q)) * (y : PadicAlgCl q) *
          ((r : M) : PadicAlgCl q)‖ < 1 := by
        rw [norm_mul, norm_mul, norm_mul]
        have h1 : ‖((w : M₀) : PadicAlgCl q) - (y : PadicAlgCl q)‖ ≤ 1 := by
          rw [← hWcoe, ← hXcoe, ← coe_sub]; exact norm_coe_le_one _
        calc ‖(q : PadicAlgCl q)‖ * ‖((w : M₀) : PadicAlgCl q) - (y : PadicAlgCl q)‖ * ‖(y : PadicAlgCl q)‖ *
              ‖((r : M) : PadicAlgCl q)‖
            ≤ ‖(q : PadicAlgCl q)‖ * ‖((w : M₀) : PadicAlgCl q) - (y : PadicAlgCl q)‖ * ‖(y : PadicAlgCl q)‖ :=
              mul_le_of_le_one_right (by positivity) (norm_coe_le_one r)
          _ ≤ ‖(q : PadicAlgCl q)‖ * ‖((w : M₀) : PadicAlgCl q) - (y : PadicAlgCl q)‖ :=
              mul_le_of_le_one_right (by positivity) hy1
          _ ≤ ‖(q : PadicAlgCl q)‖ := mul_le_of_le_one_right (norm_nonneg _) h1
          _ < 1 := norm_natCast_q_lt_one
      have hC : ‖(((w : M₀) : PadicAlgCl q) - (y : PadicAlgCl q)) ^ q‖ < 1 := by
        rw [key]
        refine lt_of_le_of_lt (norm_sub_le_max _ _) (max_lt hA hB)
      rw [norm_pow] at hC
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hq.ne_zero).mp hC
    ·
      have htN : ∀ n ∈ N, n • (∑ i ∈ Finset.range ℓ, h ^ i • y) = ∑ i ∈ Finset.range ℓ, h ^ i • y := by
        intro n hn
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun i _ => smul_fixed_of_normal N hyN (h ^ i) n hn)
      have hth : h • (∑ i ∈ Finset.range ℓ, h ^ i • y) = ∑ i ∈ Finset.range ℓ, h ^ i • y :=
        smul_sum_range_eq h ℓ hyℓ
      have htcoe : ((∑ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q) =
          ∑ i ∈ Finset.range ℓ, ((h ^ i • y : L) : PadicAlgCl q) := by push_cast; rfl
      have ht1 : ‖((∑ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q)‖ ≤ 1 := by
        rw [htcoe]
        exact norm_sum_le_one _ _ (fun i _ => by rw [norm_smul_eq hG]; exact hy1)
      have hty : ‖((∑ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q) - (ℓ : PadicAlgCl q) * (y : PadicAlgCl q)‖ < 1 := by
        have : ((∑ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q) - (ℓ : PadicAlgCl q) * (y : PadicAlgCl q) =
            ∑ i ∈ Finset.range ℓ, (((h ^ i • y : L) : PadicAlgCl q) - (y : PadicAlgCl q)) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, htcoe]
        rw [this]
        exact norm_sum_lt _ _ one_pos (fun i _ => hres i y hyN hy1)

      have hℓ1 : ‖((ℓ : ℕ) : PadicAlgCl q)‖ = 1 := norm_natCast_eq_one hℓ hℓq
      have hℓ0 : ((ℓ : ℕ) : PadicAlgCl q) ≠ 0 := fun h0 => by rw [h0, norm_zero] at hℓ1; exact zero_ne_one hℓ1
      have hfixℓ : ∀ k : G, k • ((ℓ : L)⁻¹) = (ℓ : L)⁻¹ := fun k => by
        rw [smul_inv'', ← map_natCast (algebraMap ℚ_[q] L) ℓ, hG]
      have hzcoe : ((((ℓ : L)⁻¹ * ∑ i ∈ Finset.range ℓ, h ^ i • y : L)) : PadicAlgCl q) =
          ((ℓ : ℕ) : PadicAlgCl q)⁻¹ * ((∑ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q) := by
        push_cast; rfl
      obtain ⟨z, hz⟩ := mk₀ ((ℓ : L)⁻¹ * ∑ i ∈ Finset.range ℓ, h ^ i • y)
        (fun n hn => by rw [smul_mul', hfixℓ, htN n hn])
        (by rw [smul_mul', hfixℓ, hth])
        (by rw [hzcoe, norm_mul, norm_inv, hℓ1, inv_one, one_mul]; exact ht1)
      refine ⟨z, ?_⟩
      have : ((z : M₀) : PadicAlgCl q) - (y : PadicAlgCl q) =
          ((ℓ : ℕ) : PadicAlgCl q)⁻¹ * (((∑ i ∈ Finset.range ℓ, h ^ i • y : L) : PadicAlgCl q) - (ℓ : PadicAlgCl q) * (y : PadicAlgCl q)) := by
        rw [hz, hzcoe, mul_sub, ← mul_assoc, inv_mul_cancel₀ hℓ0, one_mul]
      rw [this, norm_mul, norm_inv, hℓ1, inv_one, one_mul]
      exact hty

  have hcardle : Nat.card (ResidueField (Rw q M)) ≤ Nat.card (ResidueField (Rw q M₀)) := by
    have hcomp : ∀ z z' : Rw q M₀, residue (Rw q M₀) z = residue (Rw q M₀) z' →
        residue (Rw q M) (ι z) = residue (Rw q M) (ι z') := by
      intro z z' hzz
      apply residue_eq_of_norm_sub_lt_one
      rw [hι, hι]
      exact norm_sub_lt_one_of_residue_eq hzz
    have hrs : Function.Surjective (residue (Rw q M₀)) := IsLocalRing.residue_surjective
    refine Nat.card_le_card_of_surjective (fun ξ₀ => residue (Rw q M) (ι (Function.surjInv hrs ξ₀))) ?_
    intro ξ
    obtain ⟨X, rfl⟩ := IsLocalRing.residue_surjective ξ
    obtain ⟨z, hz⟩ := hsurj X
    refine ⟨residue (Rw q M₀) z, ?_⟩
    show residue (Rw q M) (ι (Function.surjInv hrs (residue (Rw q M₀) z))) = residue (Rw q M) X
    rw [← hz]
    exact hcomp _ _ (Function.surjInv_eq hrs _)
  have hf1 : f = 1 := by
    have hle' := hcardle
    rw [hcard] at hle'
    have h2 : 1 < Nat.card (ResidueField (Rw q M₀)) := Finite.one_lt_card
    have : f ≤ 1 := (Nat.pow_le_pow_iff_right h2).mp (by rw [pow_one]; exact hle')
    omega

  have he2 : 2 ≤ e := by
    rw [hf1, mul_one] at hef
    omega
  have hπM₀ : (π : PadicAlgCl q) ∈ M₀ := (hmemM₀ π).mpr (fun k _ => hπG k)
  have hπM : (π : PadicAlgCl q) ∈ M := hle hπM₀
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Rw q M₀, ((P₀ : M₀) : PadicAlgCl q) = (π : PadicAlgCl q) :=
    ⟨⟨⟨(π : PadicAlgCl q), hπM₀⟩, (mem_Rw_iff _).mpr hπ1.le⟩, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Rw q M, ((P : M) : PadicAlgCl q) = (π : PadicAlgCl q) :=
    ⟨⟨⟨(π : PadicAlgCl q), hπM⟩, (mem_Rw_iff _).mpr hπ1.le⟩, rfl⟩
  have hιP : ι P₀ = P := by
    apply Subtype.ext; apply Subtype.ext
    rw [hι, hP₀, hP]
  have hP₀m : P₀ ∈ maximalIdeal (Rw q M₀) := by rw [mem_maximalIdeal_iff, hP₀]; exact hπ1
  have hPme : P ∈ maximalIdeal (Rw q M) ^ e := by
    rw [← hιP, ← hmap]; exact Ideal.mem_map_of_mem ι hP₀m
  have hPm2 : P ∈ maximalIdeal (Rw q M) ^ 2 := Ideal.pow_le_pow_right he2 hPme
  have hP0 : (P : M) ≠ 0 := by
    intro h0
    have : ((P : M) : PadicAlgCl q) = 0 := by rw [h0]; rfl
    rw [hP] at this
    rw [this, norm_zero] at hπpos
    exact lt_irrefl _ hπpos

  have hmle : maximalIdeal (Rw q M) ≤ Ideal.span {P} := by
    intro Y hY
    rw [mem_maximalIdeal_iff] at hY
    obtain ⟨y', hy'Y, hy'N⟩ := hofM ((Y : M) : PadicAlgCl q) (Y : M).2
    have hYπ : ‖((Y : M) : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖ := by
      rw [← hy'Y] at hY ⊢; exact hπmax y' hy'N hY
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨(Y : M) / (P : M), ?_⟩, ?_⟩
    · rw [mem_Rw_iff]
      push_cast
      rw [hP, norm_div]
      exact div_le_one_of_le₀ hYπ (norm_nonneg _)
    · apply Subtype.ext
      show (Y : M) = (P : M) * ((Y : M) / (P : M))
      rw [mul_div_cancel₀ (Y : M) hP0]
  have hPsq : P ∈ Ideal.span {P ^ 2} := by
    rw [← Ideal.span_singleton_pow]
    exact Ideal.pow_right_mono hmle 2 hPm2
  rw [Ideal.mem_span_singleton] at hPsq
  obtain ⟨r, hr⟩ := hPsq
  have hnorm := congrArg (fun t : Rw q M => ‖((t : M) : PadicAlgCl q)‖) hr
  simp only [coe_mul, coe_pow, hP, norm_mul, norm_pow] at hnorm
  have hr1 : ‖((r : M) : PadicAlgCl q)‖ ≤ 1 := norm_coe_le_one r
  have hle2 : ‖(π : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖ ^ 2 :=
    calc ‖(π : PadicAlgCl q)‖ = ‖(π : PadicAlgCl q)‖ ^ 2 * ‖((r : M) : PadicAlgCl q)‖ := hnorm
      _ ≤ ‖(π : PadicAlgCl q)‖ ^ 2 := mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) 2) hr1
  nlinarith [hπpos, hπ1, hle2]

end S_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
end P2MW
export P2MW.S_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one (solution)
