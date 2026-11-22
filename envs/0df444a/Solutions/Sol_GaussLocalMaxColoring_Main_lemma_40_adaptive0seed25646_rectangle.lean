-- Prove2me | solution 1 for GaussLocalMaxColoring.Main.lemma_40_adaptive0seed25646_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T14:57:13.829126+00:00
-- url     : https://prove2.me/submissions/7bc43b87-0209-4f56-902d-79265687e67f

import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_0
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_1
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_2
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_3
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_4
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_5
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_6
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_7
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_8
import Theorems.Thm_GaussLocalMaxColoring_Main_lemma_40_adaptive0seed25646_b4_part_9
set_option autoImplicit false
set_option maxHeartbeats 3000000
open GaussLocalMaxColoring.Main

theorem solution (A ρ : ℝ) (hAlo : (264376411/131072000:ℝ) ≤ A) (hAhi : A ≤ (265162843/131072000:ℝ))
    (hρlo : (814129/2048000:ℝ) ≤ ρ) (hρhi : ρ ≤ (822321/2048000:ℝ)) (hcase : qA A ρ < qc ρ) :
    (∃ a b μ c κ θ : ℝ, L40Case1 A ρ a b μ c κ θ) ∧ 0 < qA A ρ/Real.sqrt (1-ρ^2) := by
  let b : ℝ := (103531361122339324647880530522418473224550678173/6474633415922124204664207433178390079472570088576:ℚ)
  let c : ℝ := (148022665013912365111/4722366482869645213696:ℚ)
  let θ : ℝ := (105113898053531722649817636563532003778556764000751/182628568201966125342452015454275643968150995402752:ℚ)
  let L : ℝ := fA A ρ/Real.sqrt (1-ρ^2)
  let J : ℝ := Da+1+1/4
  let κ : ℝ := Real.sqrt (1/4-c^2-1/10^20)
  let M : ℝ := Real.sqrt (J-L^2+1/10^18)
  let μ : ℝ := (M-θ*κ)/(1+θ)
  let a : ℝ := Real.sqrt (1-1/10^12-b^2-μ^2)

  have hstat := lemma_40_adaptive0seed25646_b4_part_0 A ρ hAlo hAhi hρlo hρhi
  change (0 ≤ a ∧ 0 ≤ μ ∧ 0 ≤ c ∧ 0 ≤ κ ∧ 0 < θ ∧ θ < 14) ∧
    (a^2+b^2+μ^2 ≤ 1-1/10^12 ∧ c^2+κ^2 ≤ 1/4-1/10^20) ∧
    capacity Da ρ+1/4+1/10^18 ≤ L^2+(μ+θ*(μ+κ))^2 at hstat
  have hiv (r : ℝ) (hrlo : -(1/2:ℝ) ≤ r) (hrhi : r ≤ 1/2-ρ) :
      fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r := by
    by_cases h1 : r ≤ (-(317/1280:ℝ))
    · have h := lemma_40_adaptive0seed25646_b4_part_1 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    by_cases h2 : r ≤ (-(149/640:ℝ))
    · have h := lemma_40_adaptive0seed25646_b4_part_2 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    by_cases h3 : r ≤ (-(1173/5120:ℝ))
    · have h := lemma_40_adaptive0seed25646_b4_part_3 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    by_cases h4 : r ≤ (-(227/1024:ℝ))
    · have h := lemma_40_adaptive0seed25646_b4_part_4 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    by_cases h5 : r ≤ (-(279/1280:ℝ))
    · have h := lemma_40_adaptive0seed25646_b4_part_5 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    by_cases h6 : r ≤ (-(539/2560:ℝ))
    · have h := lemma_40_adaptive0seed25646_b4_part_6 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    by_cases h7 : r ≤ (-(111/640:ℝ))
    · have h := lemma_40_adaptive0seed25646_b4_part_7 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    by_cases h8 : r ≤ (0:ℝ)
    · have h := lemma_40_adaptive0seed25646_b4_part_8 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
      change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
      exact h
    have h := lemma_40_adaptive0seed25646_b4_part_9 A ρ hAlo hAhi hρlo hρhi r (by linarith) (by linarith)
    change fA A r+3/10^6 ≤ l40Lhs A ρ L a b c θ r at h
    exact h
  have hq : qA A ρ = fA A ρ := by
    unfold qA at hcase ⊢
    by_cases h : qc ρ ≤ fA A ρ
    · rw [min_eq_left h] at hcase
      exact (lt_irrefl _ hcase).elim
    · exact min_eq_right (by linarith)
  have hex : L40Case1 A ρ a b μ c κ θ := by
    change L40Conds A ρ (qA A ρ/Real.sqrt (1-ρ^2)) (capacity Da ρ+1/4) 1 a b μ c κ θ
    rw [hq]
    change L40Conds A ρ L (capacity Da ρ+1/4) 1 a b μ c κ θ
    refine ⟨hstat.1,hstat.2.1,?_,?_⟩
    · simpa only [one_mul] using hstat.2.2
    · intro r hrlo hrhi _
      exact (add_le_add (min_le_right (qc r) (fA A r)) le_rfl).trans (hiv r hrlo hrhi)
  refine ⟨⟨a,b,μ,c,κ,θ,hex⟩,?_⟩
  rw [hq]
  have hbase : 0 < 1-ρ^2 := by
    have hp := mul_pos (show 0 < 1-ρ by linarith) (show 0 < 1+ρ by linarith)
    nlinarith only [hp]
  apply div_pos _ (Real.sqrt_pos.mpr hbase)
  have hF : (1201/500:ℝ) ≤ ftilde A := by
    unfold ftilde
    have hs := sq_nonneg (A-2+(13/123:ℝ))
    nlinarith only [hs]
  have hS : (4/5:ℝ) ≤ Real.sqrt (1-ρ^2) := by
    apply Real.le_sqrt_of_sq_le
    have hp := mul_nonneg (show 0 ≤ (1/2:ℝ)-ρ by linarith)
      (show 0 ≤ (1/2:ℝ)+ρ by linarith)
    nlinarith only [hp]
  have hp := mul_le_mul_of_nonneg_left hS (show 0 ≤ ftilde A by linarith)
  have hz1 : max (-(1/40:ℝ)-ρ) 0=0 := max_eq_right (by linarith)
  have hz2 : max (ρ-(1/50:ℝ)) 0=ρ-(1/50:ℝ) := max_eq_left (by linarith)
  have hz3 : max (ρ-(1/4:ℝ)) 0=ρ-(1/4:ℝ) := max_eq_left (by linarith)
  unfold fA
  rw [hz1,hz2,hz3]
  nlinarith [sq_nonneg (ρ-(1/50:ℝ)),sq_nonneg (ρ-(1/4:ℝ))]
#print axioms solution
