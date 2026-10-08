-- Prove2me | solution 1 for Erdos970.lem_sum_m_rho_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T01:17:54.546973+00:00
-- url     : https://prove2.me/submissions/51ca7480-5cb3-411f-bdad-537837a22499

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT1_ComplexAnalysis
namespace Erdos970




































lemma lem_abspos (z : ℂ) : z ≠ 0 → norm z > 0 := by
  intro h_ne_zero
  apply Real.sqrt_pos.mpr
  exact Complex.normSq_pos.mpr h_ne_zero






























































lemma lem_inDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw : w ∈ closure (ballDR R)) : norm w ≤ R := by
  rw [lem_ballDR R hR] at hw
  rw [Metric.mem_closedBall] at hw
  rw [Complex.dist_eq] at hw
  simp at hw
  exact hw

lemma lem_notinDR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw : w ∉ ballDR R) : norm w ≥ R := by
                               
  unfold ballDR at hw
                                                   
  rw [Metric.mem_ball] at hw
                                                              
  push Not at hw
                                                                     
  rw [Complex.dist_eq] at hw
                       
  simp at hw
  exact hw

lemma lem_legeR (R : ℝ) (_hR : R > 0) (w : ℂ) (hw1 : norm w ≤ R) (hw2 : norm w ≥ R) : norm w = R := by
  linarith

lemma lem_circleDR (R : ℝ) (hR : R > 0) (w : ℂ) (hw1 : w ∈ closure (ballDR R)) (hw2 : w ∉ ballDR R) : norm w = R := by
  have h1 : norm w ≤ R := lem_inDR R hR w hw1
  have h2 : norm w ≥ R := lem_notinDR R hR w hw2
  exact lem_legeR R hR w h1 h2

lemma lem_Rself (R : ℝ) (hR : R > 0) : |R| = R := by
  rw [abs_eq_self]
  linarith

lemma lem_Rself2 (R : ℝ) (hR : R > 0) : |R| ≤ R := by
  rw [lem_Rself R hR]

lemma lem_Rself3 (R : ℝ) (hR : R > 0) : (R : ℂ) ∈ closure (ballDR R) := by
  rw [lem_ballDR R hR]
  rw [Metric.mem_closedBall]
  simp
  exact lem_Rself2 R hR


lemma lem_ExtrValThm {K : Set ℂ} (hK : IsCompact K) (hK_nonempty : K.Nonempty) (g : K → ℂ) (hg : Continuous g) :
∃ v : K, ∀ z : K, norm (g z) ≤ norm (g v) := by
                                       
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
                            
  have : Nonempty K := hK_nonempty.to_subtype
                                                             
  let f : K → ℝ := fun z => norm (g z)
                                
  have hf_cont : Continuous f := continuous_norm.comp hg
                                                       
  obtain ⟨v, hv_mem, hv_max⟩ := IsCompact.exists_isMaxOn isCompact_univ Set.univ_nonempty hf_cont.continuousOn
  use v
  intro z
  exact hv_max (Set.mem_univ z)

lemma lem_ExtrValThmDR (R : ℝ) (hR : R > 0) (g : closure (ballDR R) → ℂ) (hg : Continuous g) :
∃ v : closure (ballDR R), ∀ z : closure (ballDR R), norm (g z) ≤ norm (g v) := by
                                                     
  have hK_compact : IsCompact (closure (ballDR R)) := lem_DRcompact R hR
                                             
  have hK_nonempty : (closure (ballDR R)).Nonempty := by
    rw [lem_ballDR R hR]
    rw [Metric.nonempty_closedBall]
    linarith
                                    
  exact lem_ExtrValThm hK_compact hK_nonempty g hg

lemma lem_AnalCont {R : ℝ} (_hR : R > 0) (H : ℂ → ℂ) (h_analytic : AnalyticOn ℂ H (closure (ballDR R))) :
Continuous (H ∘ (Subtype.val : closure (ballDR R) → ℂ)) := by
                                                                    
  have h_cont_on : ContinuousOn H (closure (ballDR R)) := AnalyticOn.continuousOn h_analytic
                              
  have h_val_cont : Continuous (Subtype.val : closure (ballDR R) → ℂ) := continuous_subtype_val

  exact ContinuousOn.comp_continuous h_cont_on h_val_cont (fun _ => Subtype.mem _)

lemma lem_ExtrValThmh {R : ℝ} (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ u : closure (ballDR R), ∀ z : closure (ballDR R), norm (h u) ≥ norm (h z) := by
                                                    
  have hg_continuous : Continuous (h ∘ Subtype.val : closure (ballDR R) → ℂ) :=
    lem_AnalCont hR h h_analytic
                                              
  obtain ⟨v, hv⟩ := lem_ExtrValThmDR R hR (h ∘ Subtype.val) hg_continuous
                   
  use v
                                        
  intro z
  have : norm ((h ∘ Subtype.val) z) ≤ norm ((h ∘ Subtype.val) v) := hv z
                             
  simp [Function.comp] at this
  exact this

lemma lem_MaxModP (R : ℝ) (_hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) := by
                                                             
  have h_preconnected : IsPreconnected (ballDR R) := by
    unfold ballDR
    apply Convex.isPreconnected
    exact convex_ball (0 : ℂ) R

  have h_open : IsOpen (ballDR R) := by
    unfold ballDR
    exact Metric.isOpen_ball

  have h_diff_cont : DiffContOnCl ℂ h (ballDR R) := by
    constructor
    ·                                   
      apply AnalyticOn.differentiableOn
      exact h_analytic.mono subset_closure
    ·                                         
      exact AnalyticOn.continuousOn h_analytic

  have h_max_on : IsMaxOn (norm ∘ h) (ballDR R) w := by
    intro z hz
    change ‖h z‖ ≤ ‖h w‖
    exact hw_max z hz

  have h_eq := Complex.norm_eqOn_closure_of_isPreconnected_of_isMaxOn h_preconnected h_open h_diff_cont hw_in_DR h_max_on

  intro z hz
  have norm_eq := h_eq hz
  simp only [Function.comp_apply, Function.const_apply] at norm_eq
                                                                                   
  convert (preTransparency := .instances) norm_eq

lemma lem_MaxModR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) : norm (h R) = norm (h w) := by
                                                                
  have h_const : ∀ z ∈ closure (ballDR R), norm (h z) = norm (h w) :=
    lem_MaxModP R hR h h_analytic w hw_in_DR hw_max
                                                      
  have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
                                         
  exact h_const (R : ℂ) hR_in_closure

lemma lem_MaxModRR (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (w : ℂ) (hw_in_DR : w ∈ ballDR R) (hw_max : ∀ z ∈ ballDR R, norm (h z) ≤ norm (h w)) :
∀ z ∈ closure (ballDR R), norm (h R) ≥ norm (h z) := by
  intro z hz
                                                                            
  have h1 := lem_MaxModP R hR h h_analytic w hw_in_DR hw_max z hz
                                             
  have h2 := lem_MaxModR R hR h h_analytic w hw_in_DR hw_max
                                                                             
  rw [h2, h1]

theorem lem_MaxModv2 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : closure (ballDR R), norm (v : ℂ) = R ∧ ∀ z : closure (ballDR R), norm (h (v : ℂ)) ≥ norm (h (z : ℂ)) := by
                                                       
  obtain ⟨u, hu⟩ := lem_ExtrValThmh hR h h_analytic

  if h_case : (u : ℂ) ∈ ballDR R then
                                 
    have hR_in_closure : (R : ℂ) ∈ closure (ballDR R) := lem_Rself3 R hR
    let v : closure (ballDR R) := ⟨R, hR_in_closure⟩
    use v
    constructor
    ·                
                                                                             
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                                               
      have : norm (R : ℂ) = abs R := by
        simp [Complex.norm_real]
      rw [this, lem_Rself R hR]
    ·                                                     
      intro z
                                                                        
      have hw_max : ∀ w ∈ ballDR R, norm (h w) ≤ norm (h (u : ℂ)) := by
        intro w hw
                                                      
        have hw_closure : w ∈ closure (ballDR R) := subset_closure hw
                                              
        let w_sub : closure (ballDR R) := ⟨w, hw_closure⟩
        exact hu w_sub
                                             
      have h_result := lem_MaxModRR R hR h h_analytic (u : ℂ) h_case hw_max
                                                  
      have v_eq : (v : ℂ) = (R : ℂ) := rfl
      rw [v_eq]
                                                           
      exact h_result (z : ℂ) (Subtype.mem z)
  else
                                 
    use u
    constructor
    ·                                   
      exact lem_circleDR R hR (u : ℂ) (Subtype.mem u) h_case
    ·                                                                  
      exact hu

theorem lem_MaxModv3 (R : ℝ) (hR : R > 0) (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R))) :
∃ v : ℂ, norm v = R ∧ ∀ z : ℂ, z ∈ closure (ballDR R) → norm (h v) ≥ norm (h z) := by
                                                                                   
  obtain ⟨v_sub, hv_abs, hv_max⟩ := lem_MaxModv2 R hR h h_analytic
                                                           
  let v := (v_sub : ℂ)
  use v
  constructor
  ·                
    exact hv_abs
  ·                            
    intro z hz
                                               
    have hz_sub : z ∈ closure (ballDR R) := hz
    let z_sub : closure (ballDR R) := ⟨z, hz_sub⟩
    have := hv_max z_sub
                             
    simp at this
    exact this

lemma lem_MaxModv4 (R B : ℝ) (hR : R > 0) (_hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∃ v : ℂ, norm v = R ∧ (∀ w : ℂ, w ∈ closure (ballDR R) → norm (h v) ≥ norm (h w)) ∧ norm (h v) ≤ B := by
                                                                             
  obtain ⟨v, hv_abs, hv_max⟩ := lem_MaxModv3 R hR h h_analytic
                         
  use v
  constructor
  ·           
    exact hv_abs
  constructor
  ·                                                  
    exact hv_max
  ·                                                  
    apply h_boundary_bound
    exact hv_abs

lemma lem_HardMMP (R B : ℝ) (hR : R > 0) (hB : B ≥ 0)
  (h : ℂ → ℂ) (h_analytic : AnalyticOn ℂ h (closure (ballDR R)))
  (h_boundary_bound : ∀ z : ℂ, norm z = R → norm (h z) ≤ B) :
∀ w : ℂ, w ∈ closure (ballDR R) → norm (h w) ≤ B := by
  intro w hw
                                                                                            
  obtain ⟨v, hv_abs, hv_max, hv_bound⟩ := lem_MaxModv4 R B hR hB h h_analytic h_boundary_bound
                                
  have h1 : norm (h w) ≤ norm (h v) := hv_max w hw
  have h2 : norm (h v) ≤ B := hv_bound
                             
  linarith [h1, h2]

















































































































open _root_.Complex _root_.MeasureTheory _root_.intervalIntegral
open scoped _root_.Interval











































open _root_.Filter _root_.Topology



















open _root_.Classical
                                                                                      

















open scoped _root_.Topology






























end Erdos970

end

section
-- module Solutions.OAIChowla.StrongPNT.Erdos970.PNT2_LogDerivative
namespace Erdos970




open _root_.Filter _root_.Metric _root_.Set _root_.Bornology _root_.Function


open _root_.Classical

lemma lem_frho_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    f ρ = 0 := h_rho_in_KfR1.2

lemma lem_m_rho_is_nat (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≠ ⊤ := by
  intro ρ h_rho_in_KfR1
                                           
  have hρ_closed_R1 : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                    
  have hR1_le_R : R1 ≤ R := by linarith
  have hR1_lt_one : R1 < 1 := by linarith
                       
  have hρ_ball1 : ρ ∈ Metric.ball (0 : ℂ) 1 := by
    have hdist_le : dist ρ (0 : ℂ) ≤ R1 := (Metric.mem_closedBall.mp hρ_closed_R1)
    have hdist_lt : dist ρ (0 : ℂ) < 1 := by linarith
    simpa [Metric.mem_ball] using hdist_lt
                       
  have hf_at_ρ : AnalyticAt ℂ f ρ := by
                                      
    have hsubset : Metric.closedBall (0 : ℂ) R1 ⊆ Metric.closedBall (0 : ℂ) 1 :=
      Metric.closedBall_subset_closedBall (le_of_lt hR1_lt_one)
    have hρ_closed1 : ρ ∈ Metric.closedBall (0 : ℂ) 1 := hsubset hρ_closed_R1
    exact h_f_analytic ρ hρ_closed1
                                                    
  by_contra htop
                                                           
  have h_eventually_zero : ∀ᶠ z in nhds ρ, f z = 0 := by
    have h_equiv : (analyticOrderAt f ρ = ⊤ ↔ ∀ᶠ z in nhds ρ, f z = 0) := by
      simp [analyticOrderAt, hf_at_ρ]
    exact h_equiv.mp (by simpa using htop)
                                                     
  have hf_on_ball : AnalyticOnNhd ℂ f (Metric.ball (0 : ℂ) 1) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : ℂ) 1 :=
      (Metric.ball_subset_closedBall : Metric.ball (0 : ℂ) 1 ⊆ Metric.closedBall (0 : ℂ) 1) hz
    exact h_f_analytic z hz'
                                  
  have h_preconn : IsPreconnected (Metric.ball (0 : ℂ) 1) :=
    (Metric.isConnected_ball (by exact (zero_lt_one : (0 : ℝ) < 1))).isPreconnected
                                                  
  have h_eqOn_zero : Set.EqOn f 0 (Metric.ball (0 : ℂ) 1) :=
    AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hf_on_ball h_preconn hρ_ball1
      h_eventually_zero
                                 
  have h0_in_ball : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    simp [Metric.mem_ball]
  have : f 0 = 0 := by
    have h := h_eqOn_zero h0_in_ball
    simpa [Pi.zero_apply] using h
  exact h_f_nonzero_at_zero this

lemma analyticOrderAt_ge_one_of_zero (f : ℂ → ℂ) (z : ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0) (hfinite : analyticOrderAt f z ≠ ⊤) : analyticOrderAt f z ≥ 1 := by
                                                                 
  have h_order_ne_zero : analyticOrderAt f z ≠ 0 := by
    intro h_order_zero
                                                              
    have h_f_ne_zero : f z ≠ 0 := by
      rw [← AnalyticAt.analyticOrderAt_eq_zero hf]
      exact h_order_zero
                                    
    exact h_f_ne_zero hz
                                                                      
  cases' h : analyticOrderAt f z with n
  ·                                 
                               
    rw [h] at hfinite
    exact False.elim (hfinite rfl)
  ·                                                 

    rw [h] at h_order_ne_zero
    have n_ne_zero : n ≠ 0 := by
      intro n_zero
      rw [n_zero, Nat.cast_zero] at h_order_ne_zero
      exact h_order_ne_zero rfl
                                 
    have n_ge_one : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr n_ne_zero
                            
    exact Nat.cast_le.mpr n_ge_one

lemma lem_m_rho_ge_1 (R R1 : ℝ) (hR1_pos : 0 < R1) (hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hR_lt_1 : R < 1) :
    ∀ (ρ : ℂ) (_h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f),
    analyticOrderAt f ρ ≥ 1 := by
  intro ρ h_rho_in_KfR1
                                                     
  have h_f_rho_zero : f ρ = 0 := lem_frho_zero R R1 hR1_pos hR1_lt_R f h_f_analytic ρ h_rho_in_KfR1
                                                        
  have h_order_finite : analyticOrderAt f ρ ≠ ⊤ := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 ρ h_rho_in_KfR1
                       
  have h_f_analytic_at_rho : AnalyticAt ℂ f ρ := by
    apply h_f_analytic
                                            
    have h_R1_lt_1 : R1 < 1 := by linarith
    have h_rho_in_R1 : ρ ∈ Metric.closedBall 0 R1 := h_rho_in_KfR1.1
    exact Metric.closedBall_subset_closedBall (le_of_lt h_R1_lt_1) h_rho_in_R1
                                                                          
  exact analyticOrderAt_ge_one_of_zero f ρ h_f_analytic_at_rho h_f_rho_zero h_order_finite



lemma lem_denomAnalAt (S : Finset ℂ) (n : ℂ → ℕ)
    (_hn_pos : ∀ s ∈ S, 0 < n s) (w : ℂ) (hw : w ∉ S) :
    AnalyticAt ℂ (fun z => ∏ s ∈ S, (z - s) ^ (n s)) w ∧
    (∏ s ∈ S, (w - s) ^ (n s)) ≠ 0 := by
  constructor
  ·                          
                                 
    let f : ℂ → ℂ → ℂ := fun s z => (z - s) ^ (n s)
    have h_each_analytic : ∀ s ∈ S, AnalyticAt ℂ (f s) w := by
      intro s hs
      simp only [f]
                                                               
      have h_sub : AnalyticAt ℂ (fun z => z - s) w := by
        exact AnalyticAt.sub analyticAt_id analyticAt_const
                                              
      exact h_sub.pow (n s)
    have h_prod := Finset.analyticAt_prod S h_each_analytic
    convert (preTransparency := .instances) h_prod using 1
    first | rfl | (ext z; simp [f])
  ·                                
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    apply pow_ne_zero
                     
    intro h_eq
                                         
    have h_w_eq_s : w = s := by
      rwa [← sub_eq_zero]
                                              
    rw [h_w_eq_s] at hw
    exact hw hs

lemma lem_ratioAnalAt (w : ℂ) (R R1 : ℝ) (_hR1_lt_R : R1 < R) (_hR_lt_1 : R < 1)
    (h : ℂ → ℂ) (hh : AnalyticAt ℂ h w)
    (S : Finset ℂ) (_hS : ↑S ⊆ Metric.closedBall (0 : ℂ) R1) (n : ℂ → ℕ)
    (hn_pos : ∀ s ∈ S, 0 < n s)
    (hw : w ∈ Metric.closedBall (0 : ℂ) 1 \ ↑S) :
    AnalyticAt ℂ (fun z => h z / ∏ s ∈ S, (z - s) ^ (n s)) w := by
  classical
                                                  
  have hden := lem_denomAnalAt (S := S) (n := n)
      (_hn_pos := hn_pos) (w := w)
      (hw := by simpa using hw.2)
                                                   
  exact AnalyticAt.div hh hden.1 hden.2


lemma lem_Cf_analytic_off_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) z := by

  have h_ratio_analytic : AnalyticAt ℂ (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) z := by
    apply lem_ratioAnalAt z R R1 hR1_lt_R hR_lt_1 f

    · apply h_f_analytic
      exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1

    · intro ρ hρ
      have h_mem : ρ ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hρ
      exact h_mem.1

    · intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp hs
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros

      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1)

    · constructor
      · exact Metric.closedBall_subset_closedBall (le_of_lt hR_lt_1) hz.1
      ·                                     
        intro h_z_in_finset
        have h_z_in_zeros : z ∈ zerosetKfR R1 (by linarith) f := h_finite_zeros.mem_toFinset.mp h_z_in_finset
        exact hz.2 h_z_in_zeros

  have h_eventually_eq : (fun w => f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds z]
    (fun w => Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w) := by
                                                           
    have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := hz.2
    have h_open : IsOpen (Set.compl (zerosetKfR R1 (by linarith) f)) := h_finite_zeros.isClosed.isOpen_compl
    apply Filter.eventually_of_mem (h_open.mem_nhds hz_not_in)
    intro w hw_not_in_compl
                                                              
    have hw_not_in_zeros : w ∉ zerosetKfR R1 (by linarith) f := hw_not_in_compl
                                                         
    show f w / ∏ ρ ∈ h_finite_zeros.toFinset, (w - ρ) ^ (analyticOrderAt f ρ).toNat =
         Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ w
                                                                          
    rw [Cf, dif_neg hw_not_in_zeros]

  exact h_ratio_analytic.congr h_eventually_eq

lemma lem_Cf_at_sigma_onK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z = σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ z z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  refine Filter.Eventually.of_forall ?_
  intro z hz
  subst hz
  simp [Cf, hσ]


lemma lem_Cf_at_sigma_offK0
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z /
      ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                        
  obtain ⟨h_σ_analytic, h_σ_ne_zero, h_f_eq⟩ := h_σ_spec σ hσ

  have h_σ_eventually_nonzero : ∀ᶠ z in nhds σ, h_σ σ z ≠ 0 := by
    have h_cont : ContinuousAt (h_σ σ) σ := h_σ_analytic.continuousAt
    exact h_cont.eventually_ne h_σ_ne_zero

  have h_f_eventually_nonzero : ∀ᶠ z in nhds σ, z ≠ σ → f z ≠ 0 := by
    filter_upwards [h_f_eq, h_σ_eventually_nonzero] with z h_fz_eq h_σz_nonzero
    intro hz_ne
    rw [h_fz_eq]
    apply mul_ne_zero
    · apply pow_ne_zero
      exact sub_ne_zero.mpr hz_ne
    · exact h_σz_nonzero

  have h_eventually_not_in_zeroset : ∀ᶠ z in nhds σ, z ≠ σ → z ∉ zerosetKfR R1 (by linarith) f := by
    filter_upwards [h_f_eventually_nonzero] with z h_fz_nonzero
    intro hz_ne hz_in_zeroset
    exact h_fz_nonzero hz_ne hz_in_zeroset.2

  filter_upwards [h_f_eq, h_eventually_not_in_zeroset] with z h_fz_eq h_not_in_zeroset
  intro hz_ne
                                                                    
  have hz_not_in_K : z ∉ zerosetKfR R1 (by linarith) f := h_not_in_zeroset hz_ne
                                                       
  unfold Cf
  simp [hz_not_in_K, h_fz_eq]

lemma lem_prod_no_sigma1
    {R R1 : ℝ} {hR1_pos : 0 < R1} {_hR1_lt_R : R1 < R} {_hR_lt_1 : R < 1}
    {f : ℂ → ℂ} {_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z} {_h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) (z : ℂ) :
    ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat =
    (z - σ) ^ (analyticOrderAt f σ).toNat *
    ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
  classical
  have hmem : σ ∈ h_finite_zeros.toFinset :=
    (Set.Finite.mem_toFinset (hs := h_finite_zeros)).2 hσ
  simpa using
    (Finset.mul_prod_erase (s := h_finite_zeros.toFinset)
      (f := fun ρ => (z - ρ) ^ (analyticOrderAt f ρ).toNat) (a := σ) hmem).symm


lemma lem_Cf_at_sigma_offK
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ, z ≠ σ →
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                            
  have h_cf_form := @lem_Cf_at_sigma_offK0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  filter_upwards [h_cf_form] with z h_cf_z
  intro hz_ne_sigma
                                              
  rw [h_cf_z hz_ne_sigma]
                                                 
  have h_prod_decomp := @lem_prod_no_sigma1 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ z
                                                                            
  rw [h_prod_decomp]
                                                                  
  apply mul_div_mul_left
                       
  apply pow_ne_zero
  exact sub_ne_zero.mpr hz_ne_sigma

lemma lem_Cf_at_sigma
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    ∀ᶠ z in nhds σ,
      Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
      h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
                                                 
  have h_on := @lem_Cf_at_sigma_onK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
  have h_off := @lem_Cf_at_sigma_offK R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ
                                      
  filter_upwards [h_on, h_off] with z hz_on hz_off
  by_cases h : z = σ
  ·                                                                
    have eq_result := hz_on h
                                                                  
    rw [h] at eq_result ⊢
    exact eq_result
  ·                                  
    exact hz_off h

lemma lem_h_ratio_anal
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (σ : ℂ) (_hσ : σ ∈ zerosetKfR R1 (by linarith) f)
    (g : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g σ) :
    AnalyticAt ℂ
      (fun z => g z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ),
        (z - ρ) ^ (analyticOrderAt f ρ).toNat) σ := by
                                                                             
  have hden := lem_denomAnalAt (S := h_finite_zeros.toFinset.erase σ)
    (n := fun ρ => (analyticOrderAt f ρ).toNat)
    (_hn_pos := by
      intro s hs
      have h_s_in_zeros : s ∈ zerosetKfR R1 (by linarith) f := by
        have h_mem_erase : s ∈ h_finite_zeros.toFinset.erase σ := hs
        have h_mem_orig : s ∈ h_finite_zeros.toFinset := Finset.mem_of_mem_erase h_mem_erase
        exact h_finite_zeros.mem_toFinset.mp h_mem_orig
      have h_order_ge_1 := lem_m_rho_ge_1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      have h_order_finite := lem_m_rho_is_nat R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero hR_lt_1 s h_s_in_zeros
      cases' h_cases : analyticOrderAt f s with n
      ·                    
        rw [h_cases] at h_order_finite
        exact False.elim (h_order_finite rfl)
      ·                               
        have n_ge_1 : n ≥ 1 := by
          rw [h_cases] at h_order_ge_1
          exact Nat.cast_le.mp h_order_ge_1
        simp
        exact Nat.pos_iff_ne_zero.mpr (ne_of_gt n_ge_1))
    (w := σ)
    (hw := by
      simp [Finset.mem_erase])
                                                   
  exact AnalyticAt.div hg_analytic hden.1 hden.2

lemma lem_Cf_analytic_at_K
    {R R1 : ℝ} {hR1_pos : 0 < R1} {hR1_lt_R : R1 < R} {hR_lt_1 : R < 1}
    {f : ℂ → ℂ}
    {h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z}
    {h_f_nonzero_at_zero : f 0 ≠ 0}
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (σ : ℂ) (hσ : σ ∈ zerosetKfR R1 (by linarith) f) :
    AnalyticAt ℂ (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) σ := by
                                                                               
  have h_eventually_eq := @lem_Cf_at_sigma R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec σ hσ

  obtain ⟨h_σ_analytic, _, _⟩ := h_σ_spec σ hσ
  have h_ratio_analytic := @lem_h_ratio_anal R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros σ hσ (h_σ σ) h_σ_analytic

  have h_rev_eq : (fun z => h_σ σ z / ∏ ρ ∈ (h_finite_zeros.toFinset.erase σ), (z - ρ) ^ (analyticOrderAt f ρ).toNat) =ᶠ[nhds σ]
                  (Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) := by
    filter_upwards [h_eventually_eq] with z h_z
    exact h_z.symm

  exact AnalyticAt.congr h_ratio_analytic h_rev_eq

















theorem lem_rho_in_disk_R1
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (_hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    norm ρ ≤ R1 := by
                                                                      
  have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := h_rho_in_KfR1.1
                                                                     
  rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
  simp only [sub_zero] at h_in_ball
  exact h_in_ball

theorem lem_zero_not_in_Kf (R R1 : ℝ)
  (hR1_pos : 0 < R1)
  (_hR1_lt_R : R1 < R)
  (f : ℂ → ℂ)
  (_h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z) :
    f 0 ≠ 0 → 0 ∉ zerosetKfR R1 (by linarith) f := by
  intro h_f_zero_ne_zero h_zero_in_KfR1
                                                  
  have h_f_zero_eq_zero : f 0 = 0 := h_zero_in_KfR1.2
                                                 
  exact h_f_zero_ne_zero h_f_zero_eq_zero

lemma lem_rho_ne_zero (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ ρ ∈ zerosetKfR R1 (by linarith) f, ρ ≠ 0 := by
  intro ρ h_ρ_in_zeros h_ρ_eq_zero
                                                         
  rw [h_ρ_eq_zero] at h_ρ_in_zeros
                                            
  have h_zero_not_in : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  exact h_zero_not_in h_ρ_in_zeros

lemma lem_mod_pos_iff_ne_zero (z : ℂ) : z ≠ 0 → norm z > 0 :=
  lem_abspos z

theorem lem_mod_rho_pos
    (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) :
    ∀ (ρ : ℂ), ρ ∈ zerosetKfR R1 (by linarith) f → norm ρ > 0 := by
  intro ρ h_ρ_in_zeros
                          
  have h_ρ_ne_zero : ρ ≠ 0 :=
    lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                                 
  exact lem_mod_pos_iff_ne_zero ρ h_ρ_ne_zero


lemma lem_inv_mono_decr (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) : 1 / x ≥ 1 / y := by
                                   
  have hy : 0 < y := lt_of_lt_of_le hx hxy
                                                       
  exact one_div_le_one_div_of_le hx hxy

lemma lem_inv_mod_rho_ge_inv_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (ρ : ℂ) (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    1 / norm ρ ≥ 1 / R1 := by
                                                    
  have h_abs_ρ_le_R1 : norm ρ ≤ R1 :=
    lem_rho_in_disk_R1 R R1 hR1_pos hR1_lt_R f ρ h_rho_in_KfR1
                                                            
  have h_abs_ρ_pos : norm ρ > 0 :=
    lem_mod_rho_pos R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                   
  have h_R1_pos : R1 > 0 := by
    linarith
                                                                   
  exact lem_inv_mono_decr (norm ρ) R1 h_abs_ρ_pos h_abs_ρ_le_R1


theorem lem_R_div_mod_rho_ge_R_div_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ R / R1 := by
                                             
  have h_inv_ineq : 1 / norm ρ ≥ 1 / R1 :=
    lem_inv_mod_rho_ge_inv_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1

  have h_R_div_abs_ρ_eq : R * (1 / norm ρ) = R / norm ρ := by ring
  have h_R_div_R1_eq : R * (1 / R1) = R / R1 := by ring
  rw [← h_R_div_abs_ρ_eq, ← h_R_div_R1_eq]
  exact mul_le_mul_of_nonneg_left h_inv_ineq (by linarith)

theorem lem_R_div_mod_rho_ge_R_over_R1 (R R1 : ℝ) (hR1_pos : 0 < R1)
(hR1_lt_R : R1 < R) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0) (ρ : ℂ)
    (h_rho_in_KfR1 : ρ ∈ zerosetKfR R1 (by linarith) f) :
    R / norm ρ ≥ (R/R1 : ℝ) := by
                                
  have h_ineq1 : R / norm ρ ≥ R / R1 :=
    lem_R_div_mod_rho_ge_R_div_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_rho_in_KfR1
                           
  linarith

theorem lem_mod_of_prod2 {ι : Type*} (K : Finset ι) (w : ι → ℂ) :
    ‖∏ ρ ∈ K, w ρ‖ = ∏ ρ ∈ K, ‖w ρ‖ := by
  classical
  refine Finset.induction_on K ?h0 ?hstep
  · simp
  · intro a s ha ih
                                                       
    simp [Finset.prod_insert ha, ih]

lemma lem_mod_Bf_is_prod_mod (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (_h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (z : ℂ)
    (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ)) ^ (analyticOrderAt f ρ).toNat‖ := by
                                                                          
  unfold Bf
  rw [norm_mul]
                                                                                            
  rw [lem_mod_of_prod2]
                                                                                  
  have hCf : Cf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z =
    f z / ∏ ρ ∈ h_finite_zeros.toFinset, (z - ρ) ^ (analyticOrderAt f ρ).toNat := by
    unfold Cf
    simp only [hz, ↓reduceDIte]
  rw [hCf, norm_div]
                                              
  rw [lem_mod_of_prod2]
                                                                        
  rw [div_mul_eq_mul_div]
                                                                                                    
  rw [mul_div_assoc]
                                                    
  rw [← Finset.prod_div_distrib]
  congr 2
  ext ρ
                                   
  rw [← norm_div, ← div_pow]
  congr 2
                                                  
  ring

lemma lem_abs_pow (w : ℂ) (n : ℕ) : ‖w ^ n‖ = ‖w‖ ^ n := by
  simp


lemma lem_mod_Bf_prod_mod (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
  (z : ℂ)
  (hz : z ∉ zerosetKfR R1 (by linarith) f) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ =
    ‖f z‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                 
  have h1 := lem_mod_Bf_is_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  rw [h1]
                                                              
  congr 2
  ext ρ
  rw [lem_abs_pow]

lemma lem_mod_Bf_at_0 (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      ‖((R : ℂ) / (-ρ))‖ ^ (analyticOrderAt f ρ).toNat := by
                                                                                       
  have hz0 : 0 ∉ zerosetKfR R1 (by linarith) f :=
    lem_zero_not_in_Kf R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec 0 hz0]
                                                                                  
  congr 2
  ext ρ
  congr 1
  simp only [zero_mul, zero_div, sub_zero, zero_sub]

lemma lem_mod_div_ (w1 w2 : ℂ) (_hw2_ne_zero : w2 ≠ 0) : ‖w1 / w2‖ = ‖w1‖ / ‖w2‖ := by
  simp


lemma lem_mod_div_and_neg (R : ℝ) (hR_pos : 0 < R) (ρ : ℂ) (h_rho_ne_zero : ρ ≠ 0) :
  ‖(R : ℂ) / (-ρ)‖ = R / ‖ρ‖ := by
                                                              
  have hden : (-ρ) ≠ 0 := by simpa using neg_ne_zero.mpr h_rho_ne_zero
  have hdiv := lem_mod_div_ (R : ℂ) (-ρ) hden
  calc
    ‖(R : ℂ) / (-ρ)‖ = ‖(R : ℂ)‖ / ‖-ρ‖ := hdiv
    _ = ‖(R : ℂ)‖ / ‖ρ‖ := by simp [norm_neg]
    _ = |R| / ‖ρ‖ := by simp
    _ = R / ‖ρ‖ := by simp [abs_of_pos hR_pos]

theorem lem_mod_Bf_at_0_eval  (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ =
    ‖f 0‖ * ∏ ρ ∈ h_finite_zeros.toFinset,
      (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
                               
  rw [lem_mod_Bf_at_0 R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec]
                                               
  congr 1
                                                         
  apply Finset.prod_congr rfl
  intro ρ hρ

  have h_ρ_ne_zero : ρ ≠ 0 := by
                                                             
    have h_ρ_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := by
      exact (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
    exact lem_rho_ne_zero R R1 hR1_pos hR1_lt_R f h_f_analytic h_f_nonzero_at_zero ρ h_ρ_in_zeros
                                                  
  rw [lem_mod_div_and_neg R (by linarith) ρ h_ρ_ne_zero]



lemma lem_prod_ineq {ι : Type*} (K : Finset ι) (a b : ι → ℝ)
    (h_nonneg : ∀ ρ ∈ K, 0 ≤ a ρ) (h_le : ∀ ρ ∈ K, a ρ ≤ b ρ) :
    ∏ ρ ∈ K, a ρ ≤ ∏ ρ ∈ K, b ρ := by
  exact Finset.prod_le_prod h_nonneg h_le










lemma lem_finset_prod_analyticAt {α : Type*} {S : Finset α} {g : α → ℂ → ℂ} (w : ℂ) :
  (∀ a ∈ S, AnalyticAt ℂ (g a) w) → AnalyticAt ℂ (fun z => ∏ a ∈ S, g a z) w := by
  intro h
  classical
  induction S using Finset.induction with
  | empty =>
                                                                
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | insert a s ha ih =>
                                                     
    simp only [Finset.prod_insert ha]
                                               
    apply AnalyticAt.fun_mul
    ·                        
      apply h
      exact Finset.mem_insert_self a s
    ·                                                           
      apply ih
      intro b hb
      apply h
      exact Finset.mem_insert_of_mem hb






theorem lem_Bf_is_analytic (R R1 : ℝ) (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    AnalyticOnNhd ℂ (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) (Metric.closedBall (0 : ℂ) R) := by
                                   
  intro z hz

  have h_blaschke_linear : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => (R : ℂ) - star ρ * w / (R : ℂ)) z := by
    intro ρ hρ
                                         
    have h_eq : (fun w : ℂ => (R : ℂ) - star ρ * w / (R : ℂ)) =
                (fun w : ℂ => (R : ℂ) + (-(star ρ) / (R : ℂ)) * w) := by
      funext w
      field_simp
      ring
    rw [h_eq]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)

  have h_powers : ∀ ρ ∈ h_finite_zeros.toFinset,
    AnalyticAt ℂ (fun w => ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
    intro ρ hρ
    exact (h_blaschke_linear ρ hρ).fun_pow _

  have h_product : AnalyticAt ℂ (fun w => ∏ ρ ∈ h_finite_zeros.toFinset,
      ((R : ℂ) - star ρ * w / (R : ℂ)) ^ (analyticOrderAt f ρ).toNat) z := by
                                                                       
    apply lem_finset_prod_analyticAt z
    intro ρ hρ
    apply h_powers
    exact hρ
                                                             
  by_cases hz_in : z ∈ zerosetKfR R1 (by linarith) f
  ·                                                                                 
    have h_cf_at_sigma := @lem_Cf_analytic_at_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in
                                                                          
    exact AnalyticAt.fun_mul h_cf_at_sigma h_product

  ·                                                    
    have hz_in_compl : z ∈ Metric.closedBall (0 : ℂ) R \ zerosetKfR R1 (by linarith) f := by
      constructor
      · exact hz
      · exact hz_in
    have h_cf_off := @lem_Cf_analytic_off_K R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_in_compl
    exact AnalyticAt.fun_mul h_cf_off h_product

lemma complex_mul_star_eq_norm_sq (z : ℂ) : z * star z = (‖z‖ ^ 2 : ℂ) := by
                                                      
  rw [Complex.star_def]
                                                    
  exact Complex.mul_conj' z

lemma lem_mod_Bf_eq_mod_f_on_boundary (R R1 : ℝ)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ = ‖f z‖ := by
  intro z hz
                                                                              
  have hz_not_in : z ∉ zerosetKfR R1 (by linarith) f := by
    intro h_in
                                                    
    have h_norm_le_R1 : ‖z‖ ≤ R1 := by simpa [sub_zero] using (h_in.1 : z ∈ Metric.closedBall (0 : ℂ) R1)
                                                  
    have h_norm_eq_R : ‖z‖ = R := by simpa using hz
    linarith [h_norm_le_R1, h_norm_eq_R, hR1_lt_R]
  rw [lem_mod_Bf_prod_mod R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz_not_in]

  have h_each_factor_one : ∀ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ = 1 := by
    intro ρ hρ

    have z_ne_rho : z ≠ ρ := by
      intro h_eq
      have rho_in_zeros : ρ ∈ zerosetKfR R1 (by linarith) f := (Set.Finite.mem_toFinset h_finite_zeros).mp hρ
      have rho_bound : ‖ρ‖ ≤ R1 := by
        have h_in_ball : ρ ∈ Metric.closedBall (0 : ℂ) R1 := rho_in_zeros.1
        rw [Metric.mem_closedBall, Complex.dist_eq] at h_in_ball
        simpa using h_in_ball
      have R1_lt_R : R1 < R := by linarith
      rw [← h_eq, hz] at rho_bound
      linarith [R1_lt_R]

    rw [Complex.norm_div]

    have z_conj_eq : z * star z = (R ^ 2 : ℂ) := by
      rw [complex_mul_star_eq_norm_sq z, hz, pow_two]

    have num_rewrite : (R : ℂ) - z * star ρ / (R : ℂ) = ((R : ℂ)^2 - z * star ρ) / (R : ℂ) := by
      have hRne : (R : ℂ) ≠ 0 := by exact_mod_cast (hR1_pos.trans hR1_lt_R).ne'
      field_simp [hRne]

    rw [num_rewrite, Complex.norm_div]

    have factor_eq : (R : ℂ)^2 - z * star ρ = z * star (z - ρ) := by
      rw [← z_conj_eq, star_sub]
      ring

    rw [factor_eq, Complex.norm_mul, norm_star, ←hz]
    have hRpos : 0 < R := hR1_pos.trans hR1_lt_R
    have hnorm_denom : ‖z - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr z_ne_rho)
    simp [hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hnorm_denom, hRpos.ne']

  have h_prod_one : ∏ ρ ∈ h_finite_zeros.toFinset, ‖(((R : ℂ) - z * star ρ / (R : ℂ)) / (z - ρ))‖ ^ (analyticOrderAt f ρ).toNat = 1 := by
                                        
    rw [← Finset.prod_congr rfl (fun ρ hρ => by rw [h_each_factor_one ρ hρ, one_pow])]
    rw [Finset.prod_const_one]

  rw [h_prod_one, mul_one]

lemma lem_Bf_bounded_on_boundary (B R R1 : ℝ) (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
                                             
  intro z hz
  have hz_le : ‖z‖ ≤ R := le_of_eq hz
  have h_eq :=
    lem_mod_Bf_eq_mod_f_on_boundary R R1 (by linarith) hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec z hz
  simpa [h_eq] using hf_le_B z hz_le


lemma mem_closedBall_of_norm_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) : z ∈ Metric.closedBall (0 : ℂ) R := by
  have : dist z (0 : ℂ) ≤ R := by simpa [Complex.dist_eq, sub_zero] using hz
  simpa [Metric.closedBall] using this

lemma closure_ball_eq_closedBall_center (R : ℝ) (hR : 0 < R) :
  closure (Metric.ball (0 : ℂ) R) = Metric.closedBall (0 : ℂ) R := by
  simpa using (closure_ball (x := (0 : ℂ)) (r := R) (ne_of_gt hR))

lemma lem_max_mod_principle_for_Bf (B R : ℝ) (hB : 1 < B) (hR_pos : 0 < R)
    (fB : ℂ → ℂ)
    (h_analytic : AnalyticOnNhd ℂ fB (Metric.closedBall (0 : ℂ) R))
  (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R → ‖fB z‖ ≤ B) :
  ∀ z : ℂ, ‖z‖ ≤ R → ‖fB z‖ ≤ B := by
  intro z hz
                               
  have hB0 : 0 ≤ B := le_of_lt (lt_trans zero_lt_one hB)
                                                                 
  have h_an_on_closure : AnalyticOn ℂ fB (closure (ballDR R)) := by
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using h_analytic.analyticOn
                                                                        
  have h_le :=
    lem_HardMMP R B hR_pos hB0 fB h_an_on_closure (by
      intro z hzR; exact h_bd_boundary z hzR)
                                                                                 
  have hz_cl : z ∈ closure (ballDR R) := by
    have hz_closed : z ∈ Metric.closedBall (0 : ℂ) R := mem_closedBall_of_norm_le hz
    simpa [ballDR, closure_ball_eq_closedBall_center R hR_pos] using hz_closed
  exact h_le z hz_cl

lemma lem_Bf_bounded_in_disk_from_boundary (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  have hA := lem_Bf_is_analytic R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec
  exact lem_max_mod_principle_for_Bf B R hB (by linarith)
    (Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ) hA h_bd_boundary

lemma lem_Bf_bounded_in_disk_from_f (B R R1 : ℝ)
    (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1) (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    ∀ z : ℂ, ‖z‖ ≤ R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B := by
  intro z hz
  have h_bd_boundary : ∀ z : ℂ, ‖z‖ = R →
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ z‖ ≤ B :=
    lem_Bf_bounded_on_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  exact (lem_Bf_bounded_in_disk_from_boundary B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec h_bd_boundary) z hz

lemma lem_Bf_at_0_le_M (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
  ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B := by
  have h :=
    lem_Bf_bounded_in_disk_from_f B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ h_σ_spec hf_le_B
  have h0 : ‖(0 : ℂ)‖ ≤ R := by simpa using (le_of_lt (by linarith))
  simpa using h 0 h0

lemma lem_combine_bounds_on_Bf0 (B R R1 : ℝ) (_hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hBf0 : ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
  classical
                                       
  set K := h_finite_zeros.toFinset
                                                        
  have hf0_ne0 : f 0 ≠ 0 := by simp [hf0_eq_one]
  have hf0_norm : ‖f 0‖ = 1 := by simp [hf0_eq_one]
  have h_eval0 :=
    lem_mod_Bf_at_0_eval R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec
  have h_eval_prod :
      ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖
        = ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    rw [h_eval0, hf0_norm, one_mul]
                                             
  have h_base_ge : ∀ ρ ∈ K, R / ‖ρ‖ ≥ (R/R1 : ℝ) := by
    intro ρ hρK
    have hρ_in : ρ ∈ zerosetKfR R1 (by linarith) f := by simpa [K] using hρK
    simpa using
      (lem_R_div_mod_rho_ge_R_over_R1 R R1 hR1_pos hR1_lt_R f h_f_analytic hf0_ne0 ρ hρ_in)
                                          
  have R_over_R1_nonneg : 0 ≤ R/R1 := by
    have : 0 ≤ R := by linarith
    apply div_nonneg (by assumption) (le_of_lt hR1_pos)
  have h_prod_le :
      ∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat
        ≤ ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat := by
    refine lem_prod_ineq K
      (fun ρ => (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
      (fun ρ => (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat)
      ?h_nonneg ?h_le
    · intro ρ hρK; exact pow_nonneg (R_over_R1_nonneg) _
    · intro ρ hρK
      exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ R / R1) (h_base_ge ρ hρK) _
  have h_prod_le_B :
      ∏ ρ ∈ K, (R / R1: ℝ) ^ (analyticOrderAt f ρ).toNat ≤ B := by
    have h_right : ∏ ρ ∈ K, (R / ‖ρ‖) ^ (analyticOrderAt f ρ).toNat =
        ‖Bf R R1 hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero h_finite_zeros h_σ 0‖ := by
      simp [h_eval_prod]
    exact le_trans h_prod_le (by simpa [h_right] using hBf0)
                                                                                       
  have h_prod_pow_sum :
      (∏ ρ ∈ K, (R/R1 : ℝ) ^ (analyticOrderAt f ρ).toNat)
        = (R/R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) := by
    simpa using
      (Finset.prod_pow_eq_pow_sum K (fun ρ => (analyticOrderAt f ρ).toNat) (R/R1 : ℝ))
                                                                          
  have h_natPow : (R / R1 : ℝ) ^ (∑ ρ ∈ K, (analyticOrderAt f ρ).toNat) ≤ B := by
    simpa [h_prod_pow_sum] using h_prod_le_B
                                                
  set S : ℕ := ∑ ρ ∈ K, (analyticOrderAt f ρ).toNat
  have h_natPowS : (R / R1 : ℝ) ^ S ≤ B := by simpa [S] using h_natPow
                                                     
  have h_rpowS : (R / R1 : ℝ) ^ (S : ℝ) ≤ B := by
                                                    
    simpa [(Real.rpow_natCast (R / R1 : ℝ) S)] using h_natPowS
                                                                    
  have h_cast_sum : (S : ℝ)
      = (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) := by
    simp [S]
                                       
  have : (R / R1 : ℝ) ^ (∑ ρ ∈ K, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ B := by
    simpa [h_cast_sum] using h_rpowS
  simpa [K] using this

lemma lem_jensen_inequality_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (R / R1 : ℝ) ^ (∑ ρ ∈ h_finite_zeros.toFinset, (analyticOrderAt f ρ).toNat : ℝ) ≤ B := by
                                
  have hf0_ne0 : f 0 ≠ 0 := by
    rw [hf0_eq_one]; norm_num
                                                      
  have hBf0 :=
    lem_Bf_at_0_le_M B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic hf0_ne0 h_finite_zeros h_σ h_σ_spec hf_le_B
                                                      
  let K := h_finite_zeros.toFinset
  have hres := lem_combine_bounds_on_Bf0 B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hBf0
                                                                         
  simpa using hres

lemma lem_log_mono_inc {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : Real.log x ≤ Real.log y := by
  exact Real.log_le_log hx hxy


lemma lem_jensen_log_form (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R / R1) ≤ Real.log B := by
                                               
  set S : ℝ := ∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)
                                    
  have hpow_le : (R / R1 : ℝ) ^ S ≤ B := by
    simpa [S] using
      (lem_jensen_inequality_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B)
                    
  have hbase_pos : 1 < (R / R1 : ℝ) := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have hbase_pos' : 0 < (R / R1 : ℝ) := by
    have : 0 < R := by linarith
    linarith
                                                               
  have hxpos : 0 < (R / R1 : ℝ) ^ S := by
    simpa [S] using Real.rpow_pos_of_pos hbase_pos' S
                              
  have hlog_le : Real.log ((R / R1 : ℝ) ^ S) ≤ Real.log B :=
    lem_log_mono_inc hxpos hpow_le
                           
  have hlog_rpow : Real.log ((R / R1 : ℝ) ^ S) = S * Real.log (R / R1) := by
    simpa using (Real.log_rpow hbase_pos' S)
             
  simpa [S, hlog_rpow] using hlog_le








lemma lem_sum_m_rho_bound (B R R1 : ℝ) (hB : 1 < B)
    (hR1_pos : 0 < R1)
    (hR1_lt_R : R1 < R)
    (hR_lt_1 : R < 1)
    (f : ℂ → ℂ)
    (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
    (h_f_nonzero_at_zero : f 0 ≠ 0)
    (hf0_eq_one : f 0 = 1)
    (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
    (h_σ : ℂ → (ℂ → ℂ))
    (hf_le_B : ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ B)
    (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z) :
    (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) ≤ (1/Real.log (R/R1)) * Real.log B := by
  have h_div_log : (∑ ρ ∈ h_finite_zeros.toFinset, ((analyticOrderAt f ρ).toNat : ℝ)) * Real.log (R/R1) ≤ Real.log B := by
    apply lem_jensen_log_form B R R1 hB hR1_pos hR1_lt_R hR_lt_1 f h_f_analytic h_f_nonzero_at_zero hf0_eq_one h_finite_zeros h_σ h_σ_spec hf_le_B
  have log_pos' : R/R1 > 1 := by exact (one_lt_div hR1_pos).mpr hR1_lt_R
  have log_pos : Real.log (R/R1) > 0 := by exact Real.log_pos log_pos'
  calc
    ∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat
    _ = 1 / Real.log (R / R1) * (Real.log (R / R1) * (∑ ρ ∈ h_finite_zeros.toFinset, ↑(analyticOrderAt f ρ).toNat)) := by
      field_simp [ne_of_gt log_pos]
    _ ≤ 1 / Real.log (R / R1) * Real.log B := by
      gcongr
      rw [mul_comm]
      exact h_div_log



variable {R R1 r B : ℝ} {f : ℂ → ℂ} {h_σ : ℂ → (ℂ → ℂ)}
variable (hr_pos : 0 < r) (hr_lt_R1 : r < R1) (hR1_lt_R : R1 < R) (hR_lt_1 : R < 1)
variable (hR1_pos : 0 < R1)
variable (h_f_analytic : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, AnalyticAt ℂ f z)
variable (h_f_zero : f 0 = 1)
variable (h_finite_zeros : (zerosetKfR R1 (by linarith) f).Finite)
variable (h_σ_spec : ∀ σ ∈ zerosetKfR R1 (by linarith) f,
      AnalyticAt ℂ (h_σ σ) σ ∧ h_σ σ σ ≠ 0 ∧
      ∀ᶠ z in nhds σ, f z = (z - σ) ^ (analyticOrderAt f σ).toNat * h_σ σ z)


























































































end Erdos970

end

theorem solution : type_of% @Erdos970.lem_sum_m_rho_bound := @Erdos970.lem_sum_m_rho_bound
