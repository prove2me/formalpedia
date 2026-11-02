-- Prove2me | solution 1 for CommonAgencyVCG.Algorithmic.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T07:36:33.310468+00:00
-- url     : https://prove2.me/submissions/8a33561c-418f-4e4f-93a5-a849cc227e5f

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting
import Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1

namespace Aux_CAVCG_prop4

open CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

lemma exists_aStar (S : Setting n A O) (b : Fin n → O → ℝ) : ∃ a, IsAStar S b a := by
  classical
  obtain ⟨a0, _, ha0⟩ := Finset.exists_max_image Finset.univ (fun a => Wel S a b)
    Finset.univ_nonempty
  let M := Finset.univ.filter (fun a => ∀ a', Wel S a' b ≤ Wel S a b)
  have hM : M.Nonempty := ⟨a0, by simp [M]; exact fun a' => ha0 a' (Finset.mem_univ _)⟩
  obtain ⟨a, haM, ha⟩ := Finset.exists_max_image M S.psi hM
  have haM' : ∀ a', Wel S a' b ≤ Wel S a b := by simpa [M] using haM
  refine ⟨a, haM', fun a' heq => ha a' ?_⟩
  simp only [M, Finset.mem_filter, Finset.mem_univ, true_and]
  intro a''
  rw [heq]
  exact haM' a''

lemma aStar_spec (S : Setting n A O) (b : Fin n → O → ℝ) : IsAStar S b (aStar S b) := by
  unfold aStar
  exact Classical.epsilon_spec (exists_aStar S b)

omit [Nonempty A] in
lemma E_sum (S : Setting n A O) (a : A) (b : Fin n → O → ℝ) :
    E S a (∑ ℓ, b ℓ) = ∑ ℓ, E S a (b ℓ) := by
  unfold E
  simp only [Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma implSet_aStar_nonempty (S : Setting n A O) (hS : S.Standing) (b : Fin n → O → ℝ)
    (hb : InDom S b) : (implSet S (aStar S b)).Nonempty := by
  refine ⟨∑ ℓ, b ℓ, ?_, ?_⟩
  · intro o
    rw [Finset.sum_apply]
    exact Finset.sum_nonneg (fun ℓ _ => hS.2.2.2.2.2.1 ℓ (b ℓ) (hb ℓ) o)
  · intro a'
    rw [E_sum, E_sum]
    exact (aStar_spec S b).1 a'

omit [Nonempty A] in
lemma E_cont (S : Setting n A O) (a : A) : Continuous (fun w : O → ℝ => E S a w) := by
  unfold E; fun_prop

/-- LP2 attains its infimum: for any action `a` whose implementability set is nonempty,
some `w ∈ L_a` minimizes `E_{F|a}[w]`. -/
lemma exists_min (S : Setting n A O) (hS : S.Standing) (a : A)
    (hne : (implSet S a).Nonempty) :
    ∃ w ∈ implSet S a, E S a w = kCost S a := by
  classical
  obtain ⟨w0, hw0⟩ := hne
  have hF0 := hS.2.2.1
  set c := E S a w0 with hc
  set G : O → ℝ := fun o => ∑ a', S.F a' o with hG
  set C : ℝ := ∑ a' : A, (c - S.psi a + S.psi a') with hC
  let proj : (O → ℝ) → (O → ℝ) := fun w o => if G o = 0 then 0 else w o
  have hGF : ∀ o, G o = 0 → ∀ a', S.F a' o = 0 := by
    intro o ho a'
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun a'' _ => hF0 a'' o)).1 ho a' (Finset.mem_univ _)
  have hEproj : ∀ w a', E S a' (proj w) = E S a' w := by
    intro w a'
    unfold E
    apply Finset.sum_congr rfl
    intro o _
    by_cases ho : G o = 0
    · simp [proj, ho, hGF o ho a']
    · simp [proj, ho]
  have hproj_mem : ∀ w ∈ implSet S a, proj w ∈ implSet S a := by
    intro w hw
    refine ⟨fun o => ?_, fun a' => ?_⟩
    · by_cases ho : G o = 0
      · simp [proj, ho]
      · simp only [proj, ho, if_false]; exact hw.1 o
    · rw [hEproj, hEproj]; exact hw.2 a'
  let K : Set (O → ℝ) := ({w | w ∈ implSet S a ∧ E S a w ≤ c}) ∩
    Set.pi Set.univ (fun o => Set.Icc 0 (C / G o))
  have hprojK : ∀ w ∈ implSet S a, E S a w ≤ c → proj w ∈ K := by
    intro w hw hwc
    refine ⟨⟨hproj_mem w hw, by rw [hEproj]; exact hwc⟩, ?_⟩
    intro o _
    by_cases ho : G o = 0
    · simp [proj, ho]
    · simp only [proj, ho, if_false]
      refine ⟨hw.1 o, ?_⟩
      have hGpos : 0 < G o :=
        lt_of_le_of_ne (Finset.sum_nonneg (fun a' _ => hF0 a' o)) (Ne.symm ho)
      rw [le_div_iff₀ hGpos]
      have hsum : ∑ o', G o' * w o' = ∑ a', E S a' w := by
        simp only [hG, E, Finset.sum_mul]
        exact Finset.sum_comm
      have h1 : G o * w o ≤ ∑ o', G o' * w o' :=
        Finset.single_le_sum (f := fun o' => G o' * w o')
          (fun o' _ => mul_nonneg (Finset.sum_nonneg (fun a' _ => hF0 a' o')) (hw.1 o'))
          (Finset.mem_univ o)
      have h2 : ∑ a', E S a' w ≤ C := by
        rw [hC]
        apply Finset.sum_le_sum
        intro a' _
        have := hw.2 a'
        linarith
      rw [mul_comm]
      linarith
  have hKc : IsCompact K := by
    have hpc : IsCompact (Set.pi Set.univ (fun o => Set.Icc (0 : ℝ) (C / G o))) :=
      isCompact_univ_pi (fun o => isCompact_Icc)
    apply hpc.of_isClosed_subset _ Set.inter_subset_right
    apply IsClosed.inter _ (isClosed_set_pi (fun o _ => isClosed_Icc))
    have : {w | w ∈ implSet S a ∧ E S a w ≤ c} =
        (⋂ o, {w : O → ℝ | 0 ≤ w o}) ∩
          ((⋂ a', {w : O → ℝ | E S a' w - S.psi a' ≤ E S a w - S.psi a}) ∩
            {w | E S a w ≤ c}) := by
      ext w; simp [implSet, and_assoc]
    rw [this]
    refine IsClosed.inter (isClosed_iInter fun o => isClosed_le continuous_const
      (continuous_apply o)) (IsClosed.inter (isClosed_iInter fun a' => isClosed_le
        ((E_cont S a').sub continuous_const) ((E_cont S a).sub continuous_const))
        (isClosed_le (E_cont S a) continuous_const))
  have hKne : K.Nonempty := ⟨proj w0, hprojK w0 hw0 le_rfl⟩
  obtain ⟨ws, hwsK, hmin⟩ := hKc.exists_isMinOn hKne (E_cont S a).continuousOn
  have hbdd : BddBelow (Set.range fun w : implSet S a => E S a w) := by
    refine ⟨0, ?_⟩
    rintro x ⟨⟨w, hw⟩, rfl⟩
    unfold E
    exact Finset.sum_nonneg (fun o _ => mul_nonneg (hF0 _ o) (hw.1 o))
  refine ⟨ws, hwsK.1.1, le_antisymm ?_ ?_⟩
  · haveI : Nonempty (implSet S a) := ⟨⟨w0, hw0⟩⟩
    unfold kCost
    apply le_ciInf
    rintro ⟨w, hw⟩
    show E S a ws ≤ E S a w
    by_cases hwc : E S a w ≤ c
    · have := hmin (hprojK w hw hwc)
      simp only [Set.mem_setOf_eq] at this
      rw [hEproj] at this
      exact this
    · have := hmin (hprojK w0 hw0 le_rfl)
      simp only [Set.mem_setOf_eq] at this
      rw [hEproj] at this
      linarith
  · exact ciInf_le hbdd ⟨ws, hwsK.1.1⟩

end Aux_CAVCG_prop4

open CommonAgencyVCG.Algorithmic Aux_CAVCG_prop4 in
theorem solution {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]
    (S : Setting n A O) (hS : S.Standing) (b : Fin n → O → ℝ) (hb : InDom S b) :
    ∃ w ∈ implSet S (aStar S b), E S (aStar S b) w = kCost S (aStar S b) :=
  exists_min S hS (aStar S b) (implSet_aStar_nonempty S hS b hb)
