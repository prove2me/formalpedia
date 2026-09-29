-- Prove2me | solution 1 for ExtCitation.LocalLevel.eq_of_unramified_level_of_index_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7803d735-f121-574f-8975-29d12a042184

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Theorems.Thm_ExtCitation_LocalLevel_finite_residueField_Rw
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw mem_of_unramified_level_of_forall_norm_smul_sub_lt_one finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq finite_residueField_Rw"
namespace Ws25UU
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

end ExtCitation.LocalLevel.Ws25UU

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw mem_of_unramified_level_of_forall_norm_smul_sub_lt_one finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq finite_residueField_Rw"
namespace Ws25UU
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
end ExtCitation.LocalLevel.Ws25UU

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw mem_of_unramified_level_of_forall_norm_smul_sub_lt_one finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq finite_residueField_Rw"
namespace Ws25UU
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

theorem norm_pow_sub_pow_lt_one {q : ℕ} [Fact q.Prime] (a b : PadicAlgCl q) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (hab : ‖a - b‖ < 1) (n : ℕ) : ‖a ^ n - b ^ n‖ < 1 := by
  have h := norm_prod_sub_prod_lt_one n (fun _ => a) (fun _ => b) (fun _ _ => ha) (fun _ _ => hb) (fun _ _ => hab)
  simpa only [Finset.prod_const, Finset.card_range] using h

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
end ExtCitation.LocalLevel.Ws25UU

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw mem_of_unramified_level_of_forall_norm_smul_sub_lt_one finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq finite_residueField_Rw"
namespace Ws25UU
p2m_open "ExtCitation.LocalLevel ExtCitation"
open IsLocalRing

section LevelArith

variable {q : ℕ} [Fact q.Prime]

noncomputable def inclRw {M L : IntermediateField ℚ_[q] (PadicAlgCl q)} (h : M ≤ L) : Rw q M →+* Rw q L where
  toFun X := ⟨IntermediateField.inclusion h (X : M), X.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coe_inclRw {M L : IntermediateField ℚ_[q] (PadicAlgCl q)} (h : M ≤ L) (X : Rw q M) :
    (((inclRw h X : Rw q L) : L) : PadicAlgCl q) = ((X : M) : PadicAlgCl q) := rfl

theorem ramificationIdx_eq_one {K M : IntermediateField ℚ_[q] (PadicAlgCl q)}
    (e : ℕ) (he : 0 < e) (ι : Rw q K →+* Rw q M)
    (hι : ∀ x : Rw q K, (((ι x : Rw q M) : M) : PadicAlgCl q) = ((x : K) : PadicAlgCl q))
    (hmap : Ideal.map ι (maximalIdeal (Rw q K)) = maximalIdeal (Rw q M) ^ e)
    (π : PadicAlgCl q) (hπK : π ∈ K) (hπM : π ∈ M) (hπ1 : ‖π‖ < 1) (hπ0 : 0 < ‖π‖)
    (hπmax : ∀ Y : Rw q M, ‖((Y : M) : PadicAlgCl q)‖ < 1 → ‖((Y : M) : PadicAlgCl q)‖ ≤ ‖π‖) : e = 1 := by
  by_contra hne
  have he2 : 2 ≤ e := by omega
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Rw q K, ((P₀ : K) : PadicAlgCl q) = π := ⟨⟨⟨π, hπK⟩, (mem_Rw_iff _).mpr hπ1.le⟩, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Rw q M, ((P : M) : PadicAlgCl q) = π := ⟨⟨⟨π, hπM⟩, (mem_Rw_iff _).mpr hπ1.le⟩, rfl⟩
  have hιP : ι P₀ = P := by
    apply Subtype.ext; apply Subtype.ext
    rw [hι, hP₀, hP]
  have hP₀m : P₀ ∈ maximalIdeal (Rw q K) := by rw [mem_maximalIdeal_iff, hP₀]; exact hπ1
  have hPme : P ∈ maximalIdeal (Rw q M) ^ e := by
    rw [← hιP, ← hmap]; exact Ideal.mem_map_of_mem ι hP₀m
  have hPm2 : P ∈ maximalIdeal (Rw q M) ^ 2 := Ideal.pow_le_pow_right he2 hPme
  have hP0 : (P : M) ≠ 0 := by
    intro h0
    have : ((P : M) : PadicAlgCl q) = 0 := by rw [h0]; rfl
    rw [hP] at this
    rw [this, norm_zero] at hπ0
    exact lt_irrefl _ hπ0
  have hmle : maximalIdeal (Rw q M) ≤ Ideal.span {P} := by
    intro Y hY
    rw [mem_maximalIdeal_iff] at hY
    have hYπ := hπmax Y hY
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
  have hle2 : ‖π‖ ≤ ‖π‖ ^ 2 :=
    calc ‖π‖ = ‖π‖ ^ 2 * ‖((r : M) : PadicAlgCl q)‖ := hnorm
      _ ≤ ‖π‖ ^ 2 := mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) 2) hr1
  nlinarith [hπ0, hπ1, hle2]

theorem card_filter_pow_eq_self_le {F : Type} [Field F] [DecidableEq F] (c : ℕ) (hc : 1 < c) (s : Finset F)
    (hs : ∀ z ∈ s, z ^ c = z) : s.card ≤ c := by
  have hne : (Polynomial.X ^ c - Polynomial.X : Polynomial F) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hc
  have hsub : s ⊆ (Polynomial.X ^ c - Polynomial.X : Polynomial F).roots.toFinset := by
    intro z hz
    simp only [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X, hs z hz, sub_self]
  calc s.card ≤ (Polynomial.X ^ c - Polynomial.X : Polynomial F).roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ (Polynomial.X ^ c - Polynomial.X : Polynomial F).roots.card := Multiset.toFinset_card_le _
    _ ≤ (Polynomial.X ^ c - Polynomial.X : Polynomial F).natDegree := Polynomial.card_roots' _
    _ = c := FiniteField.X_pow_card_sub_X_natDegree_eq F hc

end LevelArith
end ExtCitation.LocalLevel.Ws25UU

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw mem_of_unramified_level_of_forall_norm_smul_sub_lt_one finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq finite_residueField_Rw"
namespace Ws25UU
p2m_open "ExtCitation.LocalLevel ExtCitation"
open IsLocalRing

section Levels

variable {q : ℕ} [Fact q.Prime]
variable {L : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] L]
variable {G : Type} [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]

omit [FiniteDimensional ℚ_[q] L] [Finite G] in

theorem faithfulSMul_subgroup (H : Subgroup G) : FaithfulSMul H L :=
  ⟨fun {_ _} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) (fun x => h x))⟩

theorem natCard_residueField_fixedLevel
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (H : Subgroup G) (π : L) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ h ∈ H, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖) :
    haveI := finiteDimensional_fixedLevel hG H
    haveI := finiteDimensional_fixedLevel hG (⊤ : Subgroup G)
    Nat.card (ResidueField (Rw q (fixedLevel hG H))) = Nat.card (ResidueField (Rw q (fixedLevel hG ⊤))) ^ H.index := by
  haveI := finiteDimensional_fixedLevel hG H
  haveI := finiteDimensional_fixedLevel hG (⊤ : Subgroup G)
  haveI := faithfulSMul_subgroup (L := L) H
  have hq : q.Prime := Fact.out
  have hKM : fixedLevel hG ⊤ ≤ fixedLevel hG H := fixedLevel_mono hG le_top

  have hqL : ((q : L) : PadicAlgCl q) = (q : PadicAlgCl q) := by push_cast; rfl
  have hπpos : 0 < ‖(π : PadicAlgCl q)‖ := by
    have hfix : ∀ h ∈ H, h • (q : L) = (q : L) := fun h _ => by
      rw [← map_natCast (algebraMap ℚ_[q] L) q, hG]
    have h1 : ‖((q : L) : PadicAlgCl q)‖ < 1 := by rw [hqL]; exact norm_natCast_q_lt_one
    have h2 := hπmax (q : L) hfix h1
    have h3 : 0 < ‖((q : L) : PadicAlgCl q)‖ := by
      rw [hqL, norm_natCast_q]; exact inv_pos.mpr (by exact_mod_cast hq.pos)
    exact lt_of_lt_of_le h3 h2

  have hcountG := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG (fixedLevel hG ⊤)
    (fixedLevel_le hG ⊤) (fun x => (mem_fixedLevel_iff hG ⊤ x).trans ⟨fun h g => h g (Subgroup.mem_top g), fun h g _ => h g⟩)
  have hcountH := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L H (fun h x => hG h x)
    (fixedLevel hG H) (fixedLevel_le hG H) (fun x => (mem_fixedLevel_iff hG H x).trans ⟨fun h k => h k k.2, fun h k hk => h ⟨k, hk⟩⟩)

  obtain ⟨e, f, ι, hι, he, hf, hmap, hcard, hfin⟩ :=
    ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw q (fixedLevel hG ⊤) (fixedLevel hG H) hKM
  have hπK : (π : PadicAlgCl q) ∈ fixedLevel hG ⊤ := (mem_fixedLevel_iff hG ⊤ π).mpr (fun g _ => hπG g)
  have he1 : e = 1 := by
    refine ramificationIdx_eq_one e he ι hι hmap (π : PadicAlgCl q) hπK (hKM hπK) hπ1 hπpos (fun Y hY => ?_)
    obtain ⟨y, hyY, hyH⟩ := exists_coe_eq_of_mem_fixedLevel hG H ((Y : fixedLevel hG H) : PadicAlgCl q) (Y : fixedLevel hG H).2
    rw [← hyY] at hY ⊢
    exact hπmax y hyH hY

  have hpos : 0 < Module.finrank ℚ_[q] (fixedLevel hG ⊤) := Module.finrank_pos
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hGH : Nat.card G = Nat.card H * H.index := (Subgroup.card_mul_index H).symm
  have key : Nat.card H * H.index * Module.finrank ℚ_[q] (fixedLevel hG ⊤) =
      Nat.card H * f * Module.finrank ℚ_[q] (fixedLevel hG ⊤) := by
    calc Nat.card H * H.index * Module.finrank ℚ_[q] (fixedLevel hG ⊤) = Module.finrank ℚ_[q] L := by rw [← hGH, hcountG]
      _ = Nat.card H * f * Module.finrank ℚ_[q] (fixedLevel hG ⊤) := by rw [hcountH, hfin, he1]; ring
  have hfidx : f = H.index := (Nat.eq_of_mul_eq_mul_left hHpos (Nat.eq_of_mul_eq_mul_right hpos key)).symm
  rw [hcard, hfidx]

omit [FiniteDimensional ℚ_[q] L] [Finite G] [FaithfulSMul G L] in

theorem residue_inclRw_eq_iff {M : IntermediateField ℚ_[q] (PadicAlgCl q)} (hML : M ≤ L) (X Y : Rw q M) :
    residue (Rw q L) (inclRw hML X) = residue (Rw q L) (inclRw hML Y) ↔ residue (Rw q M) X = residue (Rw q M) Y := by
  constructor
  · intro h
    apply residue_eq_of_norm_sub_lt_one
    have := norm_sub_lt_one_of_residue_eq h
    rwa [coe_inclRw, coe_inclRw] at this
  · intro h
    apply residue_eq_of_norm_sub_lt_one
    rw [coe_inclRw, coe_inclRw]
    exact norm_sub_lt_one_of_residue_eq h

omit [FiniteDimensional ℚ_[q] L] [Finite G] [FaithfulSMul G L] in

theorem exists_finset_residues {M : IntermediateField ℚ_[q] (PadicAlgCl q)} [FiniteDimensional ℚ_[q] M] (hML : M ≤ L)
    [Finite (ResidueField (Rw q M))] [DecidableEq (ResidueField (Rw q L))] :
    ∃ A : Finset (ResidueField (Rw q L)), A.card = Nat.card (ResidueField (Rw q M)) ∧
      (∀ X : Rw q M, residue (Rw q L) (inclRw hML X) ∈ A) ∧
      (∀ z ∈ A, ∃ X : Rw q M, residue (Rw q L) (inclRw hML X) = z) ∧
      (∀ z ∈ A, z ^ Nat.card (ResidueField (Rw q M)) = z) := by
  classical
  letI : Fintype (ResidueField (Rw q M)) := Fintype.ofFinite _
  have hrs : Function.Surjective (residue (Rw q M)) := IsLocalRing.residue_surjective
  obtain ⟨F, hF⟩ : ∃ F : ResidueField (Rw q M) → ResidueField (Rw q L),
      ∀ ξ, F ξ = residue (Rw q L) (inclRw hML (Function.surjInv hrs ξ)) := ⟨_, fun _ => rfl⟩
  have hFres : ∀ X : Rw q M, F (residue (Rw q M) X) = residue (Rw q L) (inclRw hML X) := by
    intro X
    rw [hF, residue_inclRw_eq_iff]
    exact Function.surjInv_eq hrs _
  have hFinj : Function.Injective F := by
    intro ξ ξ' h
    obtain ⟨X, rfl⟩ := hrs ξ
    obtain ⟨X', rfl⟩ := hrs ξ'
    rw [hFres, hFres, residue_inclRw_eq_iff] at h
    exact h
  refine ⟨Finset.image F Finset.univ, ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hFinj, Finset.card_univ, Nat.card_eq_fintype_card]
  · intro X
    rw [Finset.mem_image]
    exact ⟨residue (Rw q M) X, Finset.mem_univ _, hFres X⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨ξ, -, rfl⟩ := hz
    obtain ⟨X, rfl⟩ := hrs ξ
    exact ⟨X, (hFres X).symm⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨ξ, -, rfl⟩ := hz
    obtain ⟨X, rfl⟩ := hrs ξ
    rw [hFres, ← map_pow, ← map_pow, residue_inclRw_eq_iff, map_pow, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card _

end Levels
end ExtCitation.LocalLevel.Ws25UU

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq LocalLevel.finite_residueField_Rw"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw mem_of_unramified_level_of_forall_norm_smul_sub_lt_one finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq finite_residueField_Rw"
namespace Ws25UU
p2m_open "ExtCitation.LocalLevel ExtCitation"
open IsLocalRing

theorem le_of_unramified_levels (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (N N' : Subgroup G) [N.Normal] [N'.Normal] (hidx : N.index = N'.index)
    (π : L) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖)
    (π' : L) (hπ'G : ∀ g : G, g • π' = π') (hπ'1 : ‖(π' : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : L, (∀ n ∈ N', n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π' : PadicAlgCl q)‖) :
    N' ≤ N := by
  classical
  intro g hg

  haveI := finiteDimensional_fixedLevel hG N
  haveI := finiteDimensional_fixedLevel hG N'
  haveI := finiteDimensional_fixedLevel hG (⊤ : Subgroup G)
  have hML : fixedLevel hG N ≤ L := fixedLevel_le hG N
  have hM'L : fixedLevel hG N' ≤ L := fixedLevel_le hG N'
  haveI := ExtCitation.LocalLevel.finite_residueField_Rw q (fixedLevel hG N)
  haveI := ExtCitation.LocalLevel.finite_residueField_Rw q (fixedLevel hG N')
  haveI := ExtCitation.LocalLevel.finite_residueField_Rw q (fixedLevel hG (⊤ : Subgroup G))

  have hc : Nat.card (ResidueField (Rw q (fixedLevel hG N))) = Nat.card (ResidueField (Rw q (fixedLevel hG N'))) := by
    rw [natCard_residueField_fixedLevel hG N π hπG hπ1 hπmax, natCard_residueField_fixedLevel hG N' π' hπ'G hπ'1 hπ'max, hidx]
  have hc1 : 1 < Nat.card (ResidueField (Rw q (fixedLevel hG N))) := Finite.one_lt_card

  obtain ⟨A, hAcard, hAmem, hAof, hApow⟩ := exists_finset_residues (L := L) (M := fixedLevel hG N) hML
  obtain ⟨A', hA'card, hA'mem, hA'of, hA'pow⟩ := exists_finset_residues (L := L) (M := fixedLevel hG N') hM'L
  have hAA' : A = A' := by
    have hU : (A ∪ A').card ≤ Nat.card (ResidueField (Rw q (fixedLevel hG N))) := by
      apply card_filter_pow_eq_self_le _ hc1
      intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact hApow z hz
      · rw [hc]; exact hA'pow z hz
    have h1 : A = A ∪ A' := Finset.eq_of_subset_of_card_le Finset.subset_union_left (by rw [hAcard]; exact hU)
    have h2 : A' = A ∪ A' := Finset.eq_of_subset_of_card_le Finset.subset_union_right (by rw [hA'card, ← hc]; exact hU)
    rw [h1, ← h2]

  refine ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one q L G hG N π hπG hπ1 hπmax g ?_
  intro x hxN hx1
  obtain ⟨X, hX⟩ : ∃ X : Rw q (fixedLevel hG N), ((X : fixedLevel hG N) : PadicAlgCl q) = (x : PadicAlgCl q) :=
    ⟨⟨⟨(x : PadicAlgCl q), (mem_fixedLevel_iff hG N x).mpr hxN⟩, (mem_Rw_iff _).mpr hx1⟩, rfl⟩
  have hXA' : residue (Rw q L) (inclRw hML X) ∈ A' := hAA' ▸ hAmem X
  obtain ⟨X', hX'⟩ := hA'of _ hXA'
  obtain ⟨x', hx'X, hx'N⟩ := exists_coe_eq_of_mem_fixedLevel hG N' ((X' : fixedLevel hG N') : PadicAlgCl q) (X' : fixedLevel hG N').2
  have hxx' : ‖(x : PadicAlgCl q) - (x' : PadicAlgCl q)‖ < 1 := by
    have := norm_sub_lt_one_of_residue_eq hX'.symm
    rw [coe_inclRw, coe_inclRw, hX, ← hx'X] at this
    exact this
  have hgx' : g • x' = x' := hx'N g hg
  have hsplit : ((g • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) =
      (((g • x : L) : PadicAlgCl q) - ((g • x' : L) : PadicAlgCl q)) + ((x' : PadicAlgCl q) - (x : PadicAlgCl q)) := by
    rw [hgx']; ring
  rw [hsplit]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · rw [norm_smul_sub hG]; exact hxx'
  · rw [← norm_neg, neg_sub]; exact hxx'

end ExtCitation.LocalLevel.Ws25UU

open ExtCitation.LocalLevel.Ws25UU in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (N N' : Subgroup G) [N.Normal] [N'.Normal] (hidx : N.index = N'.index)
    (π : L) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖)
    (π' : L) (hπ'G : ∀ g : G, g • π' = π') (hπ'1 : ‖(π' : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : L, (∀ n ∈ N', n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π' : PadicAlgCl q)‖) :
    N = N' := by
  exact le_antisymm
    (le_of_unramified_levels q L G hG N' N hidx.symm π' hπ'G hπ'1 hπ'max π hπG hπ1 hπmax)
    (le_of_unramified_levels q L G hG N N' hidx π hπG hπ1 hπmax π' hπ'G hπ'1 hπ'max)

end S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq
end P2MW
export P2MW.S_ExtCitation_LocalLevel_eq_of_unramified_level_of_index_eq (solution)
