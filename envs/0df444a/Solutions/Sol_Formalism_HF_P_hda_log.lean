-- Prove2me | solution 1 for Formalism.HF.P.hda_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:20.806797+00:00
-- url     : https://prove2.me/submissions/18adc324-86c6-487c-ab6b-653abb0b6e81

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_HostDensityArith
import Theorems.Thm_Formalism_HF_P_hda_jac_zero_iff
import Theorems.Thm_Formalism_HF_P_hda_jac_qc
import Theorems.Thm_Formalism_HF_P_hda_card_qc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset Formalism.Q3
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
namespace Formalism.HF.P
theorem _root_.solution (hAP : APLogDensity) (q : Fin 3 → ℕ) (hq : Hyp3 q) (g : Gal3) :
    LogDensity {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = ((g i : ℤˣ) : ℤ)} (1 / 8) := by
  classical
  obtain ⟨hp, hinj⟩ := hq
  have hF : ∀ i, Fact (q i).Prime := fun i => ⟨(hp i).1⟩
  have hne2 : ∀ i, q i ≠ 2 := fun i h => by have := (hp i).2; omega
  have hcop : ∀ i j, i ≠ j → Nat.Coprime (q i) (q j) := fun i j h =>
    (Nat.coprime_primes (hp i).1 (hp j).1).mpr (hinj.ne h)
  set N := q 0 * q 1 * q 2 with hN
  have hNpos : 0 < N := Nat.mul_pos (Nat.mul_pos (hp 0).1.pos (hp 1).1.pos) (hp 2).1.pos
  have : NeZero N := ⟨hNpos.ne'⟩
  set e : Fin 3 → ℤ := fun i => ((g i : ℤˣ) : ℤ) with he_def
  have he : ∀ i, e i = 1 ∨ e i = -1 := fun i => by
    rcases Int.units_eq_one_or (g i) with h | h <;> simp [he_def, h]
  have hd0 : q 0 ∣ N := Dvd.intro (q 1 * q 2) (by rw [hN]; ring)
  have hd1 : q 1 ∣ N := Dvd.intro (q 0 * q 2) (by rw [hN]; ring)
  have hd2 : q 2 ∣ N := Dvd.intro (q 0 * q 1) (by rw [hN]; ring)
  have hdvd : ∀ i, q i ∣ N := by
    intro i; fin_cases i
    exacts [hd0, hd1, hd2]

  let A : Finset (ZMod N) := univ.filter (fun a => ∀ i, jacobiSym (a.val : ℤ) (q i) = e i)
  have hval : ∀ (n : ℕ) i, jacobiSym (((n : ZMod N)).val : ℤ) (q i) = jacobiSym (n : ℤ) (q i) := by
    intro n i
    apply jacobiSym.mod_left'
    rw [ZMod.val_natCast, Int.natCast_mod, Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr (hdvd i))]
  have hmem : ∀ n : ℕ, ((∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i) ↔ (n : ZMod N) ∈ A := by
    intro n
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, hval, chiQ]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun i hni => ?_, h⟩
      have h0 : jacobiSym (n : ℤ) (q i) = 0 := (hda_jac_zero_iff (q i) n).mpr (by rw [hni])
      rw [h i] at h0
      rcases he i with h1 | h1 <;> omega
  have hunit : ∀ a ∈ A, IsUnit a := by
    intro a ha
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    rw [← ZMod.natCast_zmod_val a, ZMod.isUnit_iff_coprime]
    have hc : ∀ i, Nat.Coprime a.val (q i) := by
      intro i
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (hp i).1]
      intro hd
      have h0 := (hda_jac_zero_iff (q i) a.val).mpr hd
      rw [ha i] at h0
      rcases he i with h1 | h1 <;> omega
    exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hc 0) (hc 1)) (hc 2)

  let F : ZMod N → ZMod (q 0) × ZMod (q 1) × ZMod (q 2) := fun a =>
    ((a.val : ZMod (q 0)), (a.val : ZMod (q 1)), (a.val : ZMod (q 2)))
  have hFinj : Function.Injective F := by
    intro a b hab
    simp only [F, Prod.mk.injEq, ZMod.natCast_eq_natCast_iff] at hab
    obtain ⟨h0, h1, h2⟩ := hab
    have h01 : a.val ≡ b.val [MOD q 0 * q 1] :=
      (Nat.modEq_and_modEq_iff_modEq_mul (hcop 0 1 (by decide))).mp ⟨h0, h1⟩
    have h012 : a.val ≡ b.val [MOD N] :=
      (Nat.modEq_and_modEq_iff_modEq_mul
        (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide)))).mp ⟨h01, h2⟩
    apply ZMod.val_injective N
    unfold Nat.ModEq at h012
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h012
  have hFbij : Function.Bijective F := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hFinj, ?_⟩
    simp only [ZMod.card, Fintype.card_prod, hN, mul_assoc]
  let B : ∀ i, Finset (ZMod (q i)) := fun i => univ.filter (fun y => quadraticChar (ZMod (q i)) y = e i)
  have hcardA : A.card = (B 0).card * (B 1).card * (B 2).card := by
    have hmap : A.map ⟨F, hFinj⟩ = B 0 ×ˢ (B 1 ×ˢ B 2) := by
      ext ⟨y0, y1, y2⟩
      simp only [Finset.mem_map, Finset.mem_product, A, B, Finset.mem_filter, Finset.mem_univ,
        true_and, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨a, ha, hFa⟩
        simp only [F, Prod.mk.injEq] at hFa
        obtain ⟨r0, r1, r2⟩ := hFa
        refine ⟨?_, ?_, ?_⟩
        · rw [← r0, ← hda_jac_qc]; exact ha 0
        · rw [← r1, ← hda_jac_qc]; exact ha 1
        · rw [← r2, ← hda_jac_qc]; exact ha 2
      · rintro ⟨h0, h1, h2⟩
        obtain ⟨a, ha⟩ := hFbij.2 (y0, y1, y2)
        refine ⟨a, ?_, ha⟩
        simp only [F, Prod.mk.injEq] at ha
        obtain ⟨r0, r1, r2⟩ := ha
        intro i; fin_cases i
        · show jacobiSym (a.val : ℤ) (q 0) = e 0
          rw [hda_jac_qc, r0]; exact h0
        · show jacobiSym (a.val : ℤ) (q 1) = e 1
          rw [hda_jac_qc, r1]; exact h1
        · show jacobiSym (a.val : ℤ) (q 2) = e 2
          rw [hda_jac_qc, r2]; exact h2
    rw [← Finset.card_map ⟨F, hFinj⟩, hmap, Finset.card_product, Finset.card_product, mul_assoc]
  have hB : ∀ i, 2 * (B i).card = q i - 1 := fun i => hda_card_qc (q i) (hne2 i) (e i) (he i)
  have htot : N.totient = (q 0 - 1) * (q 1 - 1) * (q 2 - 1) := by
    rw [hN, Nat.totient_mul (Nat.Coprime.mul_left (hcop 0 2 (by decide)) (hcop 1 2 (by decide))),
      Nat.totient_mul (hcop 0 1 (by decide)), Nat.totient_prime (hp 0).1,
      Nat.totient_prime (hp 1).1, Nat.totient_prime (hp 2).1]
  have h8 : 8 * A.card = N.totient := by
    rw [hcardA, htot, ← hB 0, ← hB 1, ← hB 2]; ring
  have hphi : (0 : ℝ) < N.totient := Nat.cast_pos.mpr (Nat.totient_pos.mpr hNpos)
  have hsumconst : ∑ a ∈ A, (1 / (N.totient : ℝ)) = 1 / 8 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have h8r : (8 : ℝ) * A.card = N.totient := by exact_mod_cast h8
    have hA0 : (A.card : ℝ) ≠ 0 := by intro h0; rw [h0] at h8r; linarith
    rw [← h8r]; field_simp

  have hS : ∀ a ∈ A, LogDensity {p : ℕ | (p : ZMod N) = a} (1 / (N.totient : ℝ)) :=
    fun a ha => hAP N a (hunit a ha)
  have hind : ∀ (f : ℕ → ℝ) (n : ℕ),
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}}.indicator f n =
        ∑ a ∈ A, {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator f n := by
    intro f n
    by_cases hn : n.Prime
    · by_cases hT : (∀ i, n ≠ q i) ∧ ∀ i, chiQ (q i) n = e i
      · have ha : (n : ZMod N) ∈ A := (hmem n).1 hT
        rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧
          ∀ i, chiQ (q i) p = e i}} from ⟨hn, hT⟩), Finset.sum_eq_single_of_mem (n : ZMod N) ha]
        · rw [Set.indicator_of_mem (show n ∈ {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = (n : ZMod N)}}
            from ⟨hn, rfl⟩)]
        · intro b _ hb
          exact Set.indicator_of_notMem (fun h => hb h.2.symm) _
      · rw [Set.indicator_of_notMem (fun h => hT h.2), Finset.sum_eq_zero]
        intro b hb
        apply Set.indicator_of_notMem
        rintro ⟨_, h⟩
        have h' : (n : ZMod N) = b := h
        exact hT ((hmem n).2 (h' ▸ hb))
    · rw [Set.indicator_of_notMem (fun h => hn h.1), Finset.sum_eq_zero]
      intro b _
      exact Set.indicator_of_notMem (fun h => hn h.1) _
  have hsumm : ∀ᶠ x in 𝓝[>] (1 : ℝ), ∀ a ∈ A,
      Summable ({p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x)) := by
    rw [Filter.eventually_all_finset]
    intro a ha
    have hpos : (0 : ℝ) < 1 / (N.totient : ℝ) := by positivity
    filter_upwards [(hS a ha).eventually (lt_mem_nhds hpos)] with x hx
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns, mul_zero] at hx
    exact lt_irrefl _ hx
  have heq : (fun x : ℝ => ∑ a ∈ A, (x - 1) * (∑' n : ℕ,
      {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (p : ZMod N) = a}}.indicator
        (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)) =ᶠ[𝓝[>] (1 : ℝ)]
      (fun x : ℝ => (x - 1) * (∑' n : ℕ,
        {p : ℕ | p.Prime ∧ p ∈ {p : ℕ | (∀ i, p ≠ q i) ∧ ∀ i, chiQ (q i) p = e i}}.indicator
          (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)) := by
    filter_upwards [hsumm] with x hx
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum hx]
    congr 1
    exact tsum_congr (fun n => (hind _ n).symm)
  have hlim := tendsto_finsetSum A (fun a ha => hS a ha)
  rw [hsumconst] at hlim
  exact hlim.congr' heq
end Formalism.HF.P
