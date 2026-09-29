-- Prove2me | solution 1 for ExtCitation.LocalLevel.exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dd2d1dd4-4f8f-5f99-a3fe-25b349b14e51

import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import Theorems.Thm_ExtCitation_LocalLevel_exists_relative_ramification_inertia_Rw
import Theorems.Thm_ExtCitation_LocalLevel_mem_of_unramified_level_of_forall_norm_smul_sub_lt_one
import Theorems.Thm_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory groupCohomology ExtCitation.LocalLevel P2MW.S_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow.ExtCitation.LocalLevel"

namespace ExtCitation
p2m_export "ExtCitation" "LocalLevel.exists_relative_ramification_inertia_Rw LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace LocalLevel
p2m_export "ExtCitation.LocalLevel" "Rw exists_relative_ramification_inertia_Rw mem_of_unramified_level_of_forall_norm_smul_sub_lt_one finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq"
namespace Ws25C3a
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

end Layer

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
    try simp only at this
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

theorem coe_mul (x y : Rw q Kw) : (((x * y : Rw q Kw) : Kw) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) * ((y : Kw) : PadicAlgCl q) := by
  push_cast; rfl

theorem coe_pow (x : Rw q Kw) (n : ℕ) : (((x ^ n : Rw q Kw) : Kw) : PadicAlgCl q) = ((x : Kw) : PadicAlgCl q) ^ n := by
  push_cast; rfl

end Integers

section Ultra

variable {q : ℕ} [Fact q.Prime]

theorem norm_sub_le_max (a b : PadicAlgCl q) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max a (-b)

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

end Ultra

end ExtCitation.LocalLevel.Ws25C3a

open ExtCitation.LocalLevel.Ws25C3a IsLocalRing in
theorem solution (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hKL : K ≤ L)
    (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x)
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (φ : G) (hφ : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖((φ • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K))‖ < 1)
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖)
    (ψ : S) (hψ : ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
      ‖(((ψ : G) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ Nat.card (IsLocalRing.ResidueField (Rw q K'))‖ < 1)
    (π' : (↥L)ˣ) (hπ'S : ∀ s ∈ S, s • π' = π') (hπ'1 : ‖((π' : L) : PadicAlgCl q)‖ < 1)
    (hπ'max : ∀ y : L, (∀ n ∈ N ⊓ S, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π' : L) : PadicAlgCl q)‖) :
    ∃ e f : ℕ, 0 < e ∧ 0 < f ∧ e * f = S.index ∧
      ‖((π : L) : PadicAlgCl q)‖ = ‖((π' : L) : PadicAlgCl q)‖ ^ e ∧
      (QuotientGroup.mk' N (ψ : G) = QuotientGroup.mk' N (φ ^ f)) := by
  classical
  have hq : q.Prime := Fact.out

  have hπG' : ∀ g : G, g • (π : L) = (π : L) := fun g => by rw [← hcompat, hπG]
  have hπ'S' : ∀ s ∈ S, s • (π' : L) = (π' : L) := fun s hs => by rw [← hcompat, hπ'S s hs]

  have hKK' : K ≤ K' := by
    intro z hz
    have hzL : z ∈ L := hKL hz
    have := (hK ⟨z, hzL⟩).mp hz
    exact (hK' ⟨z, hzL⟩).mpr (fun s _ => this s)

  obtain ⟨e, f, ι, hι, he, hf, hmap, hcard, hfin⟩ :=
    ExtCitation.LocalLevel.exists_relative_ramification_inertia_Rw q K K' hKK'
  refine ⟨e, f, he, hf, ?_, ?_, ?_⟩
  ·
    have hcountG := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L G hG K hKL hK
    haveI : FaithfulSMul S L :=
      ⟨fun {s t} h => Subtype.ext (FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := L) (fun x => h x))⟩
    have hcountS := ExtCitation.LocalLevel.finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq q L S
      (fun s x => hG s x) K' hK'L (fun x => (hK' x).trans ⟨fun h s => h s s.2, fun h s hs => h ⟨s, hs⟩⟩)
    have hpos : 0 < Module.finrank ℚ_[q] K := Module.finrank_pos
    have hSpos : 0 < Nat.card S := Nat.card_pos
    have hGS : Nat.card G = Nat.card S * S.index := (Subgroup.card_mul_index S).symm

    have key : Nat.card S * S.index * Module.finrank ℚ_[q] K = Nat.card S * (e * f) * Module.finrank ℚ_[q] K := by
      calc Nat.card S * S.index * Module.finrank ℚ_[q] K = Module.finrank ℚ_[q] L := by rw [← hGS, hcountG]
        _ = Nat.card S * (e * f) * Module.finrank ℚ_[q] K := by rw [hcountS, hfin]; ring
    have := Nat.eq_of_mul_eq_mul_right hpos key
    exact (Nat.eq_of_mul_eq_mul_left hSpos this).symm
  ·
    have hπK : ((π : L) : PadicAlgCl q) ∈ K := (hK _).mpr hπG'
    have hπ'K' : ((π' : L) : PadicAlgCl q) ∈ K' := (hK' _).mpr hπ'S'
    obtain ⟨Pk, hPk⟩ : ∃ Pk : Rw q K, ((Pk : K) : PadicAlgCl q) = ((π : L) : PadicAlgCl q) :=
      ⟨⟨⟨_, hπK⟩, (mem_Rw_iff _).mpr hπ1.le⟩, rfl⟩
    obtain ⟨P', hP'⟩ : ∃ P' : Rw q K', ((P' : K') : PadicAlgCl q) = ((π' : L) : PadicAlgCl q) :=
      ⟨⟨⟨_, hπ'K'⟩, (mem_Rw_iff _).mpr hπ'1.le⟩, rfl⟩
    have hπpos : 0 < ‖((π : L) : PadicAlgCl q)‖ := by
      rw [norm_pos_iff]; intro h0
      exact π.ne_zero (by exact_mod_cast h0)
    have hπ'pos : 0 < ‖((π' : L) : PadicAlgCl q)‖ := by
      rw [norm_pos_iff]; intro h0
      exact π'.ne_zero (by exact_mod_cast h0)

    have hofK : ∀ Y : Rw q K, ∃ y : L, (y : PadicAlgCl q) = ((Y : K) : PadicAlgCl q) ∧ ∀ g : G, g • y = y := by
      intro Y
      refine ⟨⟨((Y : K) : PadicAlgCl q), hKL (Y : K).2⟩, rfl, (hK _).mp (Y : K).2⟩
    have hofK' : ∀ Y : Rw q K', ∃ y : L, (y : PadicAlgCl q) = ((Y : K') : PadicAlgCl q) ∧ ∀ s ∈ S, s • y = y := by
      intro Y
      refine ⟨⟨((Y : K') : PadicAlgCl q), hK'L (Y : K').2⟩, rfl, (hK' _).mp (Y : K').2⟩

    have hmK : maximalIdeal (Rw q K) = Ideal.span {Pk} := by
      apply le_antisymm
      · intro Y hY
        rw [mem_maximalIdeal_iff] at hY
        obtain ⟨y, hyY, hyG⟩ := hofK Y
        have hYπ : ‖((Y : K) : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖ := by
          rw [← hyY] at hY ⊢; exact hπmax y (fun n _ => hyG n) hY
        have hP0 : (Pk : K) ≠ 0 := by
          intro h0
          have : ((Pk : K) : PadicAlgCl q) = 0 := by rw [h0]; rfl
          rw [hPk] at this; rw [this, norm_zero] at hπpos; exact lt_irrefl _ hπpos
        rw [Ideal.mem_span_singleton]
        refine ⟨⟨(Y : K) / (Pk : K), ?_⟩, ?_⟩
        · rw [mem_Rw_iff]; push_cast; rw [hPk, norm_div]
          exact div_le_one_of_le₀ hYπ (norm_nonneg _)
        · apply Subtype.ext
          show (Y : K) = (Pk : K) * ((Y : K) / (Pk : K))
          rw [mul_div_cancel₀ (Y : K) hP0]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_iff, hPk]
        exact hπ1

    have hmK' : maximalIdeal (Rw q K') = Ideal.span {P'} := by
      apply le_antisymm
      · intro Y hY
        rw [mem_maximalIdeal_iff] at hY
        obtain ⟨y, hyY, hyS⟩ := hofK' Y
        have hYπ : ‖((Y : K') : PadicAlgCl q)‖ ≤ ‖((π' : L) : PadicAlgCl q)‖ := by
          rw [← hyY] at hY ⊢; exact hπ'max y (fun n hn => hyS n (Subgroup.mem_inf.mp hn).2) hY
        have hP0 : (P' : K') ≠ 0 := by
          intro h0
          have : ((P' : K') : PadicAlgCl q) = 0 := by rw [h0]; rfl
          rw [hP'] at this; rw [this, norm_zero] at hπ'pos; exact lt_irrefl _ hπ'pos
        rw [Ideal.mem_span_singleton]
        refine ⟨⟨(Y : K') / (P' : K'), ?_⟩, ?_⟩
        · rw [mem_Rw_iff]; push_cast; rw [hP', norm_div]
          exact div_le_one_of_le₀ hYπ (norm_nonneg _)
        · apply Subtype.ext
          show (Y : K') = (P' : K') * ((Y : K') / (P' : K'))
          rw [mul_div_cancel₀ (Y : K') hP0]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_maximalIdeal_iff, hP']
        exact hπ'1

    have hspan : Ideal.span {ι Pk} = Ideal.span {P' ^ e} := by
      rw [← Ideal.span_singleton_pow, ← hmK', ← hmap, hmK, Ideal.map_span, Set.image_singleton]
    rw [Ideal.span_singleton_eq_span_singleton] at hspan
    obtain ⟨u, hu⟩ := hspan
    have hnorm := congrArg (fun t : Rw q K' => ‖((t : K') : PadicAlgCl q)‖) hu
    simp only [coe_mul, coe_pow, hP', hι, hPk, norm_mul, norm_pow, norm_eq_one_of_isUnit u.isUnit, mul_one] at hnorm
    exact hnorm
  ·

    have hφpow : ∀ (j : ℕ) (x : L), (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
        ‖((φ ^ j • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ (Nat.card (ResidueField (Rw q K)) ^ j)‖ < 1 := by
      intro j x hxN hx1
      induction j with
      | zero => rw [pow_zero, one_smul, pow_zero, pow_one, sub_self, norm_zero]; exact one_pos
      | succ j ih =>
        have hsplit : ((φ ^ (j + 1) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ (Nat.card (ResidueField (Rw q K)) ^ (j + 1)) =
            (((φ • (φ ^ j • x) : L) : PadicAlgCl q) - ((φ • (x ^ (Nat.card (ResidueField (Rw q K)) ^ j)) : L) : PadicAlgCl q)) +
            (((φ • x : L) : PadicAlgCl q) ^ (Nat.card (ResidueField (Rw q K)) ^ j) -
              ((x : PadicAlgCl q) ^ Nat.card (ResidueField (Rw q K))) ^ (Nat.card (ResidueField (Rw q K)) ^ j)) := by
          rw [pow_succ', mul_smul, smul_pow', ← pow_mul, ← pow_succ']
          push_cast; ring
        rw [hsplit]
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
        · rw [norm_smul_sub hG]; push_cast; exact ih
        · refine norm_pow_sub_pow_lt_one _ _ ?_ ?_ (hφ x hxN hx1) _
          · rw [norm_smul_eq hG]; exact hx1
          · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1

    have hgres : ∀ x : L, (∀ n ∈ N, n • x = x) → ‖(x : PadicAlgCl q)‖ ≤ 1 →
        ‖((((φ ^ f)⁻¹ * (ψ : G)) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q)‖ < 1 := by
      intro x hxN hx1
      have h1 := hψ x (fun n hn => hxN n (Subgroup.mem_inf.mp hn).1) hx1
      rw [hcard] at h1
      have h2 := hφpow f x hxN hx1
      have h3 : ‖(((ψ : G) • x : L) : PadicAlgCl q) - ((φ ^ f • x : L) : PadicAlgCl q)‖ < 1 := by
        have : (((ψ : G) • x : L) : PadicAlgCl q) - ((φ ^ f • x : L) : PadicAlgCl q) =
            ((((ψ : G) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ (Nat.card (ResidueField (Rw q K)) ^ f)) -
            (((φ ^ f • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) ^ (Nat.card (ResidueField (Rw q K)) ^ f)) := by ring
        rw [this]
        exact lt_of_le_of_lt (norm_sub_le_max _ _) (max_lt h1 h2)
      have : ((((φ ^ f)⁻¹ * (ψ : G)) • x : L) : PadicAlgCl q) - (x : PadicAlgCl q) =
          (((φ ^ f)⁻¹ • ((ψ : G) • x) : L) : PadicAlgCl q) - (((φ ^ f)⁻¹ • (φ ^ f • x) : L) : PadicAlgCl q) := by
        rw [mul_smul, inv_smul_smul]
      rw [this, norm_smul_sub hG]
      exact h3
    have hmem := ExtCitation.LocalLevel.mem_of_unramified_level_of_forall_norm_smul_sub_lt_one q L G hG N (π : L) hπG' hπ1
      hπmax ((φ ^ f)⁻¹ * (ψ : G)) hgres
    exact (QuotientGroup.eq.mpr hmem).symm

end S_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow
end P2MW
export P2MW.S_ExtCitation_LocalLevel_exists_ramificationIdx_inertiaDeg_mk_eq_mk_pow (solution)
