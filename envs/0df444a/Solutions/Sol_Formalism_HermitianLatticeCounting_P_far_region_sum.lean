-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.far_region_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:35.440028+00:00
-- url     : https://prove2.me/submissions/819352ad-db06-4433-a3a3-190b75a3235c

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_minimum_linear_form
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_farW_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_farA_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_farA_zero_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_exp_neg_one_le_half
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_farA_sum_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Classical
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : FarSum := by
  intro ι Γ _ _ S d A B h ε q hq hA hB hε hεq hBε h32 h16 hd0 hdε hcount
  have hε2 : 0 < ε ^ 2 := by positivity
  have hh : 0 ≤ h := by
    by_contra hneg
    push Not at hneg
    have : h * ε ^ 2 < 0 := mul_neg_of_neg_of_pos hneg hε2
    linarith
  have hex : ∀ x : ℝ, ∃ i : ℕ, x ≤ 2 ^ i * ε := by
    intro x
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / ε) (one_lt_two : (1:ℝ) < 2)
    exact ⟨n, by rw [div_lt_iff₀ hε] at hn; exact hn.le⟩
  obtain ⟨idx, hidx1, hidx2⟩ : ∃ idx : ℝ → ℕ, (∀ x, x ≤ 2 ^ idx x * ε) ∧
      (∀ x k, idx x = k + 1 → 2 ^ k * ε < x) := by
    refine ⟨fun x => Nat.find (hex x), fun x => Nat.find_spec (hex x), ?_⟩
    intro x k hk
    have := Nat.find_min (hex x) (m := k) (by simp only at hk; omega)
    exact not_le.mp this
  have hidx0 : ∀ x, ε < x → 1 ≤ idx x := by
    intro x hx
    by_contra hc
    have h0 : idx x = 0 := by omega
    have := hidx1 x
    rw [h0] at this
    simp at this
    linarith
  have hW : ∀ x, 0 ≤ x → Real.exp (-(decExp h q x)) ≤ farW h ε (idx x) := by
    intro x hx
    rcases hk : idx x with _ | k
    · show _ ≤ (1:ℝ)
      rw [Real.exp_le_one_iff]
      have : 0 ≤ decExp h q x :=
        mul_nonneg (by linarith) (le_min (sq_nonneg _) (div_nonneg hx (Real.sqrt_nonneg _)))
      linarith
    · have h1 := hidx2 x k hk
      show _ ≤ Real.exp (-(h / 8 * (ε * (2 ^ k * ε))))
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      have hεx : ε ≤ x := by
        have : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
        nlinarith
      have h2 := minimum_linear_form q ε x hq hε hεq hεx
      unfold decExp
      calc h / 8 * (ε * (2 ^ k * ε)) ≤ h / 8 * (ε * x) := by gcongr
        _ ≤ _ := by gcongr
  have hw0 : ∀ γ, 0 ≤ ∏ v, Real.exp (-(decExp h q (d γ v))) :=
    fun γ => Finset.prod_nonneg fun v _ => (Real.exp_pos _).le
  have hwW : ∀ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤ ∏ v, farW h ε (idx (d γ v)) :=
    fun γ hγ => Finset.prod_le_prod (fun v _ => (Real.exp_pos _).le) (fun v _ => hW _ (hd0 γ hγ v))
  generalize hwdef : (fun γ => ∏ v, Real.exp (-(decExp h q (d γ v)))) = w at *
  have hw0' : ∀ γ, 0 ≤ w γ := fun γ => by rw [← hwdef]; exact hw0 γ
  have hwW' : ∀ γ ∈ S, w γ ≤ ∏ v, farW h ε (idx (d γ v)) := fun γ hγ => by
    rw [← hwdef]; exact hwW γ hγ
  show ∑ γ ∈ S, w γ ≤ _
  set m := S.sup (fun γ => univ.sup (fun v => idx (d γ v))) with hmdef
  have hm : ∀ γ ∈ S, ∀ v, idx (d γ v) ≤ m := by
    intro γ hγ v
    calc idx (d γ v) ≤ univ.sup (fun v => idx (d γ v)) :=
          Finset.le_sup (f := fun v => idx (d γ v)) (Finset.mem_univ v)
      _ ≤ m := Finset.le_sup (f := fun γ => univ.sup (fun v => idx (d γ v))) hγ
  have hT1 : Real.exp (-(h * ε ^ 2 / 16)) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_one_le_half
    linarith
  have hv0 : ∀ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ
      ≤ A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2)) := by
    intro v₀
    set t : ι → Finset ℕ := fun v => if v = v₀ then Ico 1 (m+1) else range (m+1) with ht
    have hmaps : ∀ γ ∈ S.filter (fun γ => ε < d γ v₀),
        (fun v => idx (d γ v)) ∈ Fintype.piFinset t := by
      intro γ hγ
      have hγ' := Finset.mem_filter.mp hγ
      rw [Fintype.mem_piFinset]
      intro v
      simp only [ht]
      split_ifs with hv
      · subst hv
        exact Finset.mem_Ico.mpr ⟨hidx0 _ hγ'.2, Nat.lt_succ_of_le (hm γ hγ'.1 v)⟩
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hm γ hγ'.1 v))
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ I ∈ Fintype.piFinset t,
          ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter (fun γ => (fun v => idx (d γ v)) = I), w γ
        ≤ ∑ I ∈ Fintype.piFinset t, A * ∏ v, farA B h ε (I v) := by
          apply Finset.sum_le_sum
          intro I _
          have hmem : ∀ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
              (fun γ => (fun v => idx (d γ v)) = I), γ ∈ S ∧ ∀ v, idx (d γ v) = I v := by
            intro γ hγ
            have h1 := Finset.mem_filter.mp hγ
            exact ⟨(Finset.mem_filter.mp h1.1).1, fun v => congrFun h1.2 v⟩
          have hPW : 0 ≤ ∏ v, farW h ε (I v) := Finset.prod_nonneg fun v _ => farW_nonneg _ _ _
          calc ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I), w γ
              ≤ ∑ γ ∈ (S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I), ∏ v, farW h ε (I v) := by
                apply Finset.sum_le_sum
                intro γ hγ
                obtain ⟨h1, h2⟩ := hmem γ hγ
                have := hwW' γ h1
                simp only [h2] at this
                exact this
            _ = (((S.filter (fun γ => ε < d γ v₀)).filter
                (fun γ => (fun v => idx (d γ v)) = I)).card : ℝ) * ∏ v, farW h ε (I v) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (A * Real.exp (B * ∑ v, 2 ^ (I v) * ε)) * ∏ v, farW h ε (I v) := by
                apply mul_le_mul_of_nonneg_right _ hPW
                refine le_trans ?_ (hcount (fun v => 2 ^ (I v) * ε) (fun v => by positivity))
                have hsub : (S.filter (fun γ => ε < d γ v₀)).filter
                    (fun γ => (fun v => idx (d γ v)) = I) ⊆
                    S.filter (fun γ => ∀ v, d γ v ≤ 2 ^ (I v) * ε) := by
                  intro γ hγ
                  obtain ⟨h1, h2⟩ := hmem γ hγ
                  refine Finset.mem_filter.mpr ⟨h1, fun v => ?_⟩
                  rw [← h2 v]; exact hidx1 _
                exact_mod_cast Finset.card_le_card hsub
            _ = A * ∏ v, farA B h ε (I v) := by
                unfold farA
                rw [Finset.mul_sum, Real.exp_sum, Finset.prod_mul_distrib]; ring
      _ = A * ∏ v, ∑ i ∈ t v, farA B h ε i := by
          rw [← Finset.mul_sum, Finset.prod_univ_sum]
      _ ≤ A * ∏ v, (4 * if v = v₀ then Real.exp (-(h * ε ^ 2 / 16)) / 2 else 1) := by
          apply mul_le_mul_of_nonneg_left _ hA
          apply Finset.prod_le_prod
          · intro v _; exact Finset.sum_nonneg fun i _ => farA_nonneg _ _ _ _
          · intro v _
            have hs := farA_sum_succ (B := B) hε h32 h16 m
            simp only [ht]
            split_ifs with hv
            · rw [Finset.sum_Ico_eq_sum_range]
              simp only [Nat.add_sub_cancel, add_comm 1]
              linarith
            · rw [Finset.sum_range_succ']
              have := farA_zero_le (h := h) hBε
              linarith
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_ite_eq']
          simp
  calc ∑ γ ∈ S, w γ ≤ ∑ γ ∈ S, ∑ v₀, (if ε < d γ v₀ then w γ else 0) := by
        apply Finset.sum_le_sum
        intro γ hγ
        obtain ⟨v, hv⟩ := hdε γ hγ
        calc w γ = (if ε < d γ v then w γ else 0) := by rw [if_pos hv]
          _ ≤ _ := Finset.single_le_sum (f := fun v₀ => if ε < d γ v₀ then w γ else 0)
              (fun v _ => by
                show 0 ≤ if ε < d γ v then w γ else 0
                split_ifs
                · exact hw0' γ
                · exact le_rfl) (Finset.mem_univ v)
    _ = ∑ v₀, ∑ γ ∈ S, (if ε < d γ v₀ then w γ else 0) := Finset.sum_comm
    _ = ∑ v₀, ∑ γ ∈ S.filter (fun γ => ε < d γ v₀), w γ := by simp_rw [Finset.sum_filter]
    _ ≤ ∑ _v₀ : ι, A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2)) :=
        Finset.sum_le_sum fun v₀ _ => hv0 v₀
    _ = Fintype.card ι * (A * (4 ^ Fintype.card ι * (Real.exp (-(h * ε ^ 2 / 16)) / 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ _ := by
        have h0 : 0 ≤ A * 4 ^ Fintype.card ι * Fintype.card ι * Real.exp (-(h * ε ^ 2 / 16)) := by
          positivity
        nlinarith
end Formalism.HermitianLatticeCounting.P
