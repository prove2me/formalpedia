-- Prove2me | solution 1 for CtxInvOpt.Greedy.theorem2_greedy_linear_regret
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T13:11:07.628265+00:00
-- url     : https://prove2.me/submissions/3e07244c-9e1a-4402-a705-6b817f9fe094

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry
import Definitions.Def_CtxInvOpt_Greedy_Online
import Definitions.Def_CtxInvOpt_Greedy_Policy

set_option autoImplicit false

open Real

namespace CtxGreedyLB

open CtxInvOpt.Offline CtxInvOpt.Greedy

theorem mem_unitSphere_iff {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ unitSphere d ↔ ‖x‖ = 1 := by
  simp [unitSphere]

theorem vecAngle_unit {d : ℕ} {c x : EuclideanSpace ℝ (Fin d)} (hc : ‖c‖ = 1) (hx : ‖x‖ = 1) :
    vecAngle c x = Real.arccos (inner ℝ c x) := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  simp [vecAngle, hc0, hx0, hc, hx]

theorem vecAngle_nonneg {d : ℕ} (c x : EuclideanSpace ℝ (Fin d)) : 0 ≤ vecAngle c x := by
  unfold vecAngle
  split_ifs
  · exact le_refl _
  · exact Real.arccos_nonneg _

theorem vecAngle_le_pi {d : ℕ} (c x : EuclideanSpace ℝ (Fin d)) : vecAngle c x ≤ π := by
  unfold vecAngle
  split_ifs
  · exact Real.pi_pos.le
  · exact Real.arccos_le_pi _

theorem inner_mem_Icc {d : ℕ} {c x : EuclideanSpace ℝ (Fin d)} (hc : ‖c‖ = 1) (hx : ‖x‖ = 1) :
    -1 ≤ inner ℝ c x ∧ inner ℝ c x ≤ 1 := by
  have h := abs_real_inner_le_norm c x
  rw [hc, hx, one_mul] at h
  exact abs_le.mp h

theorem circ_char {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d)))
    (hK : K ⊆ unitSphere d) (e1 e2 : EuclideanSpace ℝ (Fin d)) (h1 : e1 ∈ K) (h2 : e2 ∈ K)
    (hne : e1 + e2 ≠ 0)
    (hall : ∀ c ∈ K, inner ℝ e1 (e1 + e2) ≤ inner ℝ c (e1 + e2)) :
    uncAngle K < π / 2 ∧ ∀ chat, IsCircumcenter K chat ↔ chat = ‖e1 + e2‖⁻¹ • (e1 + e2) := by
  haveI : Nonempty K := ⟨⟨e1, h1⟩⟩
  have hMpos : 0 < ‖e1 + e2‖ := norm_pos_iff.mpr hne
  have hmnorm : ‖‖e1 + e2‖⁻¹ • (e1 + e2)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hMpos.ne']
  have hn1 : ‖e1‖ = 1 := (mem_unitSphere_iff _).mp (hK h1)
  have hn2 : ‖e2‖ = 1 := (mem_unitSphere_iff _).mp (hK h2)
  have hnK : ∀ c ∈ K, ‖c‖ = 1 := fun c hc => (mem_unitSphere_iff _).mp (hK hc)
  have he12 : inner ℝ e2 (e1 + e2) = inner ℝ e1 (e1 + e2) := by
    rw [inner_add_right, inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
      hn1, hn2, real_inner_comm]
    ring
  have hMM : inner ℝ (e1 + e2) (e1 + e2) = 2 * inner ℝ e1 (e1 + e2) := by
    rw [inner_add_left (𝕜 := ℝ) e1 e2 (e1 + e2), he12]
    ring
  have hMMn : inner ℝ (e1 + e2) (e1 + e2) = ‖e1 + e2‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hsm : ∀ c, inner ℝ c (‖e1 + e2‖⁻¹ • (e1 + e2)) = ‖e1 + e2‖⁻¹ * inner ℝ c (e1 + e2) :=
    fun c => real_inner_smul_right _ _ _
  have hbdd : ∀ chat : EuclideanSpace ℝ (Fin d),
      BddAbove (Set.range fun c : K => vecAngle (c : EuclideanSpace ℝ (Fin d)) chat) := by
    intro chat
    refine ⟨π, ?_⟩
    rintro _ ⟨c, rfl⟩
    exact vecAngle_le_pi _ _
  have hSnn : ∀ chat : EuclideanSpace ℝ (Fin d),
      0 ≤ ⨆ c : K, vecAngle (c : EuclideanSpace ℝ (Fin d)) chat := by
    intro chat
    exact le_ciSup_of_le (hbdd chat) ⟨e1, h1⟩ (vecAngle_nonneg _ _)
  have hSm : (⨆ c : K, vecAngle (c : EuclideanSpace ℝ (Fin d)) (‖e1 + e2‖⁻¹ • (e1 + e2))) =
      Real.arccos (inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2))) := by
    apply le_antisymm
    · apply ciSup_le
      rintro ⟨c, hc⟩
      rw [vecAngle_unit (hnK c hc) hmnorm]
      apply Real.arccos_le_arccos
      rw [hsm, hsm]
      exact mul_le_mul_of_nonneg_left (hall c hc) (inv_nonneg.mpr hMpos.le)
    · have := le_ciSup (hbdd (‖e1 + e2‖⁻¹ • (e1 + e2))) ⟨e1, h1⟩
      rw [vecAngle_unit hn1 hmnorm] at this
      exact this
  have hle : ∀ chat : EuclideanSpace ℝ (Fin d), ‖chat‖ = 1 →
      (⨆ c : K, vecAngle (c : EuclideanSpace ℝ (Fin d)) chat) ≤
        Real.arccos (inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2))) →
      chat = ‖e1 + e2‖⁻¹ • (e1 + e2) := by
    intro chat hc hS
    have a1 : Real.arccos (inner ℝ e1 chat) ≤ Real.arccos (inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2))) := by
      rw [← vecAngle_unit hn1 hc]
      exact (le_ciSup (hbdd chat) ⟨e1, h1⟩).trans hS
    have a2 : Real.arccos (inner ℝ e2 chat) ≤ Real.arccos (inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2))) := by
      rw [← vecAngle_unit hn2 hc]
      exact (le_ciSup (hbdd chat) ⟨e2, h2⟩).trans hS
    have i1 : inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2)) ≤ inner ℝ e1 chat := by
      by_contra hlt
      push Not at hlt
      have := Real.arccos_lt_arccos (inner_mem_Icc hn1 hc).1 hlt (inner_mem_Icc hn1 hmnorm).2
      linarith
    have i2 : inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2)) ≤ inner ℝ e2 chat := by
      by_contra hlt
      push Not at hlt
      have hlt' : inner ℝ e2 chat < inner ℝ e2 (‖e1 + e2‖⁻¹ • (e1 + e2)) := by
        rw [hsm, he12, ← hsm]; exact hlt
      have := Real.arccos_lt_arccos (inner_mem_Icc hn2 hc).1 hlt' (inner_mem_Icc hn2 hmnorm).2
      rw [hsm, he12, ← hsm] at this
      linarith
    have hsum : ‖e1 + e2‖ ≤ inner ℝ (e1 + e2) chat := by
      rw [inner_add_left]
      have h3 : 2 * inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2)) = ‖e1 + e2‖ := by
        rw [hsm, mul_left_comm, ← hMM, hMMn]
        field_simp
      linarith
    have hcm : 1 ≤ inner ℝ chat (‖e1 + e2‖⁻¹ • (e1 + e2)) := by
      rw [hsm, real_inner_comm]
      rw [le_inv_mul_iff₀ hMpos, mul_one]
      exact hsum
    have hsq := norm_sub_sq_real chat (‖e1 + e2‖⁻¹ • (e1 + e2))
    rw [hc, hmnorm] at hsq
    have h0 : ‖chat - ‖e1 + e2‖⁻¹ • (e1 + e2)‖ ^ 2 ≤ 0 := by rw [hsq]; linarith
    have h00 : ‖chat - ‖e1 + e2‖⁻¹ • (e1 + e2)‖ = 0 := by
      have := norm_nonneg (chat - ‖e1 + e2‖⁻¹ • (e1 + e2))
      nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp h00)
  have hmS : ‖e1 + e2‖⁻¹ • (e1 + e2) ∈ unitSphere d := (mem_unitSphere_iff _).mpr hmnorm
  have hunc : uncAngle K = Real.arccos (inner ℝ e1 (‖e1 + e2‖⁻¹ • (e1 + e2))) := by
    unfold uncAngle
    haveI : Nonempty (unitSphere d) := ⟨⟨_, hmS⟩⟩
    apply le_antisymm
    · have hbb : BddBelow (Set.range fun chat : unitSphere d =>
          ⨆ c : K, vecAngle (c : EuclideanSpace ℝ (Fin d)) (chat : EuclideanSpace ℝ (Fin d))) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨x, rfl⟩
        exact hSnn _
      exact (ciInf_le hbb ⟨_, hmS⟩).trans hSm.le
    · apply le_ciInf
      rintro ⟨chat, hchat⟩
      by_contra hlt
      push Not at hlt
      have heq := hle chat ((mem_unitSphere_iff _).mp hchat) hlt.le
      simp only at hlt
      rw [heq, hSm] at hlt
      exact lt_irrefl _ hlt
  constructor
  · rw [hunc, Real.arccos_lt_pi_div_two, hsm]
    have : 0 < inner ℝ e1 (e1 + e2) := by
      have : 0 < ‖e1 + e2‖ ^ 2 := by positivity
      linarith
    positivity
  · intro chat
    constructor
    · rintro ⟨hs, heq⟩
      rw [hunc] at heq
      exact hle chat ((mem_unitSphere_iff _).mp hs) heq.le
    · intro h
      rw [h]
      exact ⟨hmS, by rw [hunc]; exact hSm⟩

/-! ## Concrete geometry: an arc of a small circle in `S³` -/

noncomputable def pt (l : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(3/5 : ℝ) * Real.cos l, (3/5) * Real.sin l, 4/5]

noncomputable def cutv (μ h : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(4/5 : ℝ) * Real.cos μ, (4/5) * Real.sin μ, -(3/5) * Real.cos h]

theorem inner_pt_pt (a b : ℝ) :
    inner ℝ (pt a) (pt b) = 9/25 * Real.cos (a - b) + 16/25 := by
  rw [pt, pt, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_three, Real.cos_sub]
  ring

theorem inner_cutv_pt (μ h l : ℝ) :
    inner ℝ (cutv μ h) (pt l) = 12/25 * (Real.cos (l - μ) - Real.cos h) := by
  rw [cutv, pt, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_three, Real.cos_sub]
  ring

theorem norm_pt (l : ℝ) : ‖pt l‖ = 1 := by
  have h := inner_pt_pt l l
  rw [sub_self, Real.cos_zero, real_inner_self_eq_norm_sq] at h
  have h2 : ‖pt l‖ ^ 2 = 1 := by rw [h]; norm_num
  have h3 := norm_nonneg (pt l)
  apply le_antisymm <;> nlinarith

theorem norm_cutv_le (μ h : ℝ) : ‖cutv μ h‖ ≤ 1 := by
  have h1 : inner ℝ (cutv μ h) (cutv μ h) = 16/25 + 9/25 * Real.cos h ^ 2 := by
    rw [cutv, EuclideanSpace.inner_toLp_toLp]
    simp [dotProduct, Fin.sum_univ_three]
    nlinarith [Real.sin_sq_add_cos_sq μ]
  rw [real_inner_self_eq_norm_sq] at h1
  have hc := Real.cos_sq_le_one h
  have h2 : ‖cutv μ h‖ ^ 2 ≤ 1 := by rw [h1]; nlinarith
  nlinarith [norm_nonneg (cutv μ h)]

theorem continuous_pt : Continuous pt := by
  unfold pt
  fun_prop

theorem pt_add_ne (a b : ℝ) : pt a + pt b ≠ 0 := by
  intro h
  have h1 : inner ℝ (pt a) (pt a + pt b) = 0 := by rw [h, inner_zero_right]
  rw [inner_add_right, inner_pt_pt, inner_pt_pt] at h1
  have := Real.neg_one_le_cos (a - b)
  rw [sub_self, Real.cos_zero] at h1
  linarith

theorem cos_ge_of_abs_le {x h : ℝ} (hx : |x| ≤ h) (hπ : h ≤ π) : Real.cos h ≤ Real.cos x := by
  rw [← Real.cos_abs x]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) hπ hx

theorem abs_le_of_cos_ge {x h : ℝ} (hxπ : |x| ≤ π) (h0 : 0 ≤ h) (hc : Real.cos h ≤ Real.cos x) :
    |x| ≤ h := by
  by_contra hlt
  push Not at hlt
  have := Real.cos_lt_cos_of_nonneg_of_le_pi h0 hxπ hlt
  rw [Real.cos_abs] at this
  linarith

theorem arc_props (b : ℝ) (hb1 : 1/2 ≤ b) (hb2 : b ≤ 1) (K : Set (EuclideanSpace ℝ (Fin 3)))
    (hK1 : pt (-1) ∈ K) (hK2 : pt b ∈ K) (hKsub : K ⊆ pt '' Set.Icc (-1) b) :
    uncAngle K < π / 2 ∧
      ∀ chat, IsCircumcenter K chat ↔ chat = ‖pt (-1) + pt b‖⁻¹ • (pt (-1) + pt b) := by
  apply circ_char K _ _ _ hK1 hK2 (pt_add_ne _ _)
  · intro c hc
    obtain ⟨l, ⟨hl1, hl2⟩, rfl⟩ := hKsub hc
    rw [inner_add_right, inner_add_right, inner_pt_pt, inner_pt_pt, inner_pt_pt, inner_pt_pt]
    have hπ : (3 : ℝ) < π := Real.pi_gt_three
    set μ := (b - 1) / 2 with hμ
    set h := (b + 1) / 2 with hh
    have e1 : l - -1 = (l - μ) + h := by rw [hμ, hh]; ring
    have e2 : l - b = (l - μ) - h := by rw [hμ, hh]; ring
    have e3 : (-1 : ℝ) - b = -(2 * h) := by rw [hh]; ring
    have e4 : (-1 : ℝ) - -1 = 0 := by ring
    have key : ∀ A, Real.cos (A + h) + Real.cos (A - h) = 2 * Real.cos A * Real.cos h := by
      intro A; rw [Real.cos_add, Real.cos_sub]; ring
    rw [e1, e2, e3, e4, Real.cos_neg, Real.cos_two_mul, Real.cos_zero]
    have hk := key (l - μ)
    have hch : 0 ≤ Real.cos h := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith)
      (by linarith)
    have habs : |l - μ| ≤ h := by
      rw [abs_le]; constructor <;> linarith
    have hcc := cos_ge_of_abs_le habs (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hcc hch]
  · intro c hc
    obtain ⟨l, -, rfl⟩ := hKsub hc
    exact (mem_unitSphere_iff _).mpr (norm_pt l)

end CtxGreedyLB

open CtxGreedyLB CtxInvOpt.Offline in
open Real CtxInvOpt.Greedy in
theorem solution {n : ℕ} (hn : 1 ≤ n) :
    ∃ C0 : Set (EuclideanSpace ℝ (Fin 3)), IsClosed C0 ∧ C0 ⊆ CtxInvOpt.Offline.unitSphere 3 ∧ C0.Nonempty ∧
      CtxInvOpt.Offline.uncAngle C0 < π / 2 ∧
      ∃ κ : ℝ, 0 < κ ∧ ∀ T : ℕ, 1 ≤ T →
        ∃ cstar ∈ C0, ∃ (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 3)),
          (∀ t, CtxInvOpt.Offline.IsActionSet (X t)) ∧ (∀ t, CtxInvOpt.Offline.IsContext (f t)) ∧
          (∃ xpi xstar chat, IsGreedyRun C0 cstar X f xpi xstar chat) ∧
          ∀ xpi xstar chat, IsGreedyRun C0 cstar X f xpi xstar chat →
            κ * (T : ℝ) ≤ cumRegret cstar f xpi xstar T := by
  have hπ : (3 : ℝ) < π := Real.pi_gt_three
  have hC0sub : pt '' Set.Icc (-1) 1 ⊆ CtxInvOpt.Offline.unitSphere 3 := by
    rintro _ ⟨l, -, rfl⟩
    exact (mem_unitSphere_iff _).mpr (norm_pt l)
  have harc0 := arc_props 1 (by norm_num) le_rfl (pt '' Set.Icc (-1) 1)
    ⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩ ⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩ le_rfl
  refine ⟨pt '' Set.Icc (-1) 1, (isCompact_Icc.image continuous_pt).isClosed, hC0sub,
    ⟨pt 0, 0, ⟨by norm_num, by norm_num⟩, rfl⟩, harc0.1,
    12/25 * (Real.cos (1/4) - Real.cos (3/4)), ?_, ?_⟩
  · have : Real.cos (3/4) < Real.cos (1/4) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) (by norm_num)
    nlinarith
  intro T hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  -- the data
  set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by rw [he, EuclideanSpace.norm_single]; simp
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, hen]; norm_num
  set b : ℕ → ℝ := fun j => 1 - (j : ℝ) / (2 * T) with hb
  have hb_bounds : ∀ j, j ≤ T → 1/2 ≤ b j ∧ b j ≤ 1 := by
    intro j hj
    have hj' : (j : ℝ) ≤ T := by exact_mod_cast hj
    have h0 : 0 ≤ (j : ℝ) / (2 * T) := by positivity
    have h1 : (j : ℝ) / (2 * T) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    simp only [hb]
    constructor <;> linarith
  have hb_anti : ∀ i j, i ≤ j → b j ≤ b i := by
    intro i j hij
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    simp only [hb]
    have : (i : ℝ) / (2 * T) ≤ (j : ℝ) / (2 * T) := by gcongr
    linarith
  have hb_step : ∀ t, b t - b (t + 1) = 1 / (2 * T) := by
    intro t
    simp only [hb]
    push_cast
    field_simp
    ring
  set vv : ℕ → EuclideanSpace ℝ (Fin 3) := fun s =>
    if s < T then cutv ((b (s + 1) - 1) / 2) ((b (s + 1) + 1) / 2) else 0 with hvv
  set X : ℕ → Set (EuclideanSpace ℝ (Fin n)) := fun _ => {0, e} with hX
  set f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin 3) :=
    fun s x => inner ℝ e x • vv s with hf
  have hf0 : ∀ s, f s 0 = 0 := by intro s; simp [hf]
  have hfe : ∀ s, f s e = vv s := by intro s; simp only [hf, hee, one_smul]
  have hvnorm : ∀ s, ‖vv s‖ ≤ 1 := by
    intro s
    simp only [hvv]
    split_ifs
    · exact norm_cutv_le _ _
    · simp
  -- inner product of a cut with a point of the arc
  have hvpt : ∀ s, s < T → ∀ l, inner ℝ (vv s) (pt l) =
      12/25 * (Real.cos (l - (b (s + 1) - 1) / 2) - Real.cos ((b (s + 1) + 1) / 2)) := by
    intro s hs l
    simp only [hvv, if_pos hs]
    exact inner_cutv_pt _ _ _
  have hvκ : ∀ s, s < T → 12/25 * (Real.cos (1/4) - Real.cos (3/4)) ≤ inner ℝ (vv s) (pt 0) := by
    intro s hs
    rw [hvpt s hs]
    obtain ⟨hb1, hb2⟩ := hb_bounds (s + 1) hs
    have hc1 : Real.cos (1/4) ≤ Real.cos (0 - (b (s + 1) - 1) / 2) := by
      apply cos_ge_of_abs_le _ (by linarith)
      rw [abs_le]; constructor <;> linarith
    have hc2 : Real.cos ((b (s + 1) + 1) / 2) ≤ Real.cos (3/4) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) (by linarith)
    nlinarith
  have hκpos : 0 < 12/25 * (Real.cos (1/4) - Real.cos (3/4)) := by
    have : Real.cos (3/4) < Real.cos (1/4) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num) (by linarith) (by norm_num)
    nlinarith
  have hvpos : ∀ s, vv s = 0 ∨ 0 < inner ℝ (vv s) (pt 0) := by
    intro s
    by_cases hs : s < T
    · exact Or.inr (lt_of_lt_of_le hκpos (hvκ s hs))
    · left; simp only [hvv, if_neg hs]
  -- the expert's choice is forced where the cut is nontrivial
  have hxstar : ∀ xs : ℕ → EuclideanSpace ℝ (Fin n),
      (∀ s, xs s ∈ argminSet (pt 0) (X s) (f s)) → ∀ s, s < T → xs s = 0 := by
    intro xs hxs s hs
    obtain ⟨hmem, hmin⟩ := hxs s
    rcases hmem with h0 | he'
    · exact h0
    · exfalso
      have := hmin 0 (by simp [hX])
      rw [he', hfe, hf0, inner_zero_left] at this
      have := lt_of_lt_of_le hκpos (hvκ s hs)
      linarith
  -- the knowledge set does not depend on the run
  have hK : ∀ xs : ℕ → EuclideanSpace ℝ (Fin n),
      (∀ s, xs s ∈ argminSet (pt 0) (X s) (f s)) → ∀ t,
      knowledgeSet (pt '' Set.Icc (-1) 1) X f xs t =
        {c | c ∈ pt '' Set.Icc (-1) 1 ∧ ∀ s < t, 0 ≤ inner ℝ (vv s) c} := by
    intro xs hxs t
    ext c
    simp only [knowledgeSet, Set.mem_setOf_eq]
    apply and_congr_right
    intro _
    apply forall_congr'
    intro s
    apply imp_congr_right
    intro _
    by_cases hs : s < T
    · rw [hxstar xs hxs s hs, hf0, inner_zero_left]
      constructor
      · intro h
        have := h e (by simp [hX])
        rwa [hfe] at this
      · intro h x hx
        rcases hx with rfl | rfl
        · rw [hf0, inner_zero_left]
        · rwa [hfe]
    · have hv0 : vv s = 0 := by simp only [hvv, if_neg hs]
      have hfz : ∀ x, f s x = 0 := by intro x; simp only [hf, hv0, smul_zero]
      simp [hfz, hv0]
  -- the knowledge sets are arcs
  have hKarc : ∀ t, pt (-1) ∈ {c | c ∈ pt '' Set.Icc (-1) 1 ∧ ∀ s < t, 0 ≤ inner ℝ (vv s) c} ∧
      pt (b (min t T)) ∈ {c | c ∈ pt '' Set.Icc (-1) 1 ∧ ∀ s < t, 0 ≤ inner ℝ (vv s) c} ∧
      {c | c ∈ pt '' Set.Icc (-1) 1 ∧ ∀ s < t, 0 ≤ inner ℝ (vv s) c} ⊆
        pt '' Set.Icc (-1) (b (min t T)) := by
    intro t
    obtain ⟨hbj1, hbj2⟩ := hb_bounds (min t T) (min_le_right _ _)
    refine ⟨⟨⟨-1, ⟨le_rfl, by norm_num⟩, rfl⟩, ?_⟩, ⟨⟨b (min t T), ⟨by linarith, hbj2⟩, rfl⟩, ?_⟩, ?_⟩
    · intro s _
      by_cases hs : s < T
      · rw [hvpt s hs]
        have : (-1 : ℝ) - (b (s + 1) - 1) / 2 = -((b (s + 1) + 1) / 2) := by ring
        rw [this, Real.cos_neg, sub_self, mul_zero]
      · simp only [hvv, if_neg hs, inner_zero_left, le_refl]
    · intro s hst
      by_cases hs : s < T
      · rw [hvpt s hs]
        obtain ⟨hs1, hs2⟩ := hb_bounds (s + 1) hs
        have hle : b (min t T) ≤ b (s + 1) := hb_anti _ _ (le_min hst hs)
        have hc := cos_ge_of_abs_le (x := b (min t T) - (b (s + 1) - 1) / 2)
          (h := (b (s + 1) + 1) / 2) (by rw [abs_le]; constructor <;> linarith) (by linarith)
        nlinarith
      · simp only [hvv, if_neg hs, inner_zero_left, le_refl]
    · rintro c ⟨⟨l, ⟨hl1, hl2⟩, rfl⟩, hcut⟩
      refine ⟨l, ⟨hl1, ?_⟩, rfl⟩
      rcases Nat.eq_zero_or_pos (min t T) with h0 | hpos
      · rw [h0]; simpa [hb] using hl2
      · obtain ⟨s, hs⟩ : ∃ s, min t T = s + 1 := ⟨min t T - 1, by omega⟩
        have hst : s < t := by have := min_le_left t T; omega
        have hsT : s < T := by have := min_le_right t T; omega
        have := hcut s hst
        rw [hvpt s hsT] at this
        obtain ⟨hs1, hs2⟩ := hb_bounds (s + 1) hsT
        have hcos : Real.cos ((b (s + 1) + 1) / 2) ≤ Real.cos (l - (b (s + 1) - 1) / 2) := by
          nlinarith
        have habs := abs_le_of_cos_ge (by rw [abs_le]; constructor <;> linarith) (by linarith) hcos
        rw [abs_le] at habs
        rw [hs]
        linarith [habs.2]
  -- circumcenters
  set m : ℕ → EuclideanSpace ℝ (Fin 3) := fun t =>
    ‖pt (-1) + pt (b (min t T))‖⁻¹ • (pt (-1) + pt (b (min t T))) with hm
  have hcirc : ∀ xs : ℕ → EuclideanSpace ℝ (Fin n),
      (∀ s, xs s ∈ argminSet (pt 0) (X s) (f s)) → ∀ t chat,
      IsCircumcenter (knowledgeSet (pt '' Set.Icc (-1) 1) X f xs t) chat ↔ chat = m t := by
    intro xs hxs t chat
    rw [hK xs hxs t]
    obtain ⟨hbj1, hbj2⟩ := hb_bounds (min t T) (min_le_right _ _)
    obtain ⟨h1, h2, h3⟩ := hKarc t
    exact (arc_props _ hbj1 hbj2 _ h1 h2 h3).2 chat
  have hvm : ∀ t, t < T → inner ℝ (vv t) (m t) < 0 := by
    intro t ht
    have hmin : min t T = t := min_eq_left ht.le
    simp only [hm, hmin]
    rw [real_inner_smul_right, inner_add_right, hvpt t ht, hvpt t ht]
    have hpos : 0 < ‖pt (-1) + pt (b t)‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (pt_add_ne _ _))
    obtain ⟨hs1, hs2⟩ := hb_bounds (t + 1) ht
    obtain ⟨ht1, ht2⟩ := hb_bounds t ht.le
    have e1 : (-1 : ℝ) - (b (t + 1) - 1) / 2 = -((b (t + 1) + 1) / 2) := by ring
    rw [e1, Real.cos_neg]
    have hstep := hb_step t
    have hd : 0 < 1 / (2 * (T : ℝ)) := by positivity
    have hc : Real.cos (b t - (b (t + 1) - 1) / 2) < Real.cos ((b (t + 1) + 1) / 2) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) (by linarith) (by linarith)
    have : 12 / 25 * (Real.cos ((b (t + 1) + 1) / 2) - Real.cos ((b (t + 1) + 1) / 2)) +
        12 / 25 * (Real.cos (b t - (b (t + 1) - 1) / 2) - Real.cos ((b (t + 1) + 1) / 2)) < 0 := by
      nlinarith
    exact mul_neg_of_pos_of_neg hpos this
  have hvm' : ∀ t, inner ℝ (vv t) (m t) ≤ 0 := by
    intro t
    by_cases ht : t < T
    · exact (hvm t ht).le
    · simp only [hvv, if_neg ht, inner_zero_left, le_refl]
  have hxs0 : ∀ s, (0 : EuclideanSpace ℝ (Fin n)) ∈ argminSet (pt 0) (X s) (f s) := by
    intro s
    refine ⟨by simp [hX], ?_⟩
    intro y hy
    rw [hf0, inner_zero_left]
    rcases hy with rfl | rfl
    · rw [hf0, inner_zero_left]
    · rw [hfe]
      rcases hvpos s with h | h
      · rw [h, inner_zero_left]
      · exact h.le
  refine ⟨pt 0, ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩, X, f, ?_, ?_, ?_, ?_⟩
  · -- action sets
    intro t
    refine ⟨⟨0, by simp [hX]⟩, (Set.toFinite _).isCompact, ?_⟩
    simp only [hX]
    rw [Metric.diam_pair, dist_eq_norm, zero_sub, norm_neg, hen]
  · -- contexts are 1-Lipschitz
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, dist_eq_norm]
    simp only [hf]
    rw [← sub_smul, ← inner_sub_right, norm_smul, Real.norm_eq_abs, NNReal.coe_one, one_mul]
    have h1 := abs_real_inner_le_norm e (x - y)
    rw [hen, one_mul] at h1
    calc |inner ℝ e (x - y)| * ‖vv t‖ ≤ ‖x - y‖ * 1 :=
          mul_le_mul h1 (hvnorm t) (norm_nonneg _) (norm_nonneg _)
      _ = ‖x - y‖ := mul_one _
  · -- a run exists
    refine ⟨fun _ => e, fun _ => 0, m, ?_⟩
    intro t
    refine ⟨(hcirc (fun _ => 0) hxs0 t (m t)).mpr rfl, ⟨by simp [hX], ?_⟩, hxs0 t⟩
    intro y hy
    rw [hfe]
    rcases hy with rfl | rfl
    · rw [hf0, inner_zero_left]; exact hvm' t
    · rw [hfe]
  · -- every run has linear regret
    intro xpi xstar chat hrun
    have hxs : ∀ s, xstar s ∈ argminSet (pt 0) (X s) (f s) := fun s => (hrun s).2.2
    unfold cumRegret
    have hterm : ∀ t ∈ Finset.range T, 12/25 * (Real.cos (1/4) - Real.cos (3/4)) ≤
        inner ℝ (f t (xpi t) - f t (xstar t)) (pt 0) := by
      intro t ht
      have ht' : t < T := Finset.mem_range.mp ht
      have hch : chat t = m t := (hcirc xstar hxs t (chat t)).mp (hrun t).1
      have hxpi : xpi t = e := by
        obtain ⟨hmem, hmin⟩ := (hrun t).2.1
        rcases hmem with h0 | he'
        · exfalso
          have := hmin e (by simp [hX])
          rw [h0, hf0, hfe, inner_zero_left, hch] at this
          have := hvm t ht'
          linarith
        · exact he'
      rw [hxpi, hxstar xstar hxs t ht', hfe, hf0, sub_zero]
      exact hvκ t ht'
    calc 12/25 * (Real.cos (1/4) - Real.cos (3/4)) * (T : ℝ)
        = ∑ t ∈ Finset.range T, 12/25 * (Real.cos (1/4) - Real.cos (3/4)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum hterm
