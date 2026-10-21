-- Prove2me | solution 1 for CtxInvOpt.Greedy.lemma2_circumcenter_exists_unique
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:45:03.368376+00:00
-- url     : https://prove2.me/submissions/add84560-a033-4777-8a93-c737aac8feeb

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

set_option autoImplicit false
open CtxInvOpt.Offline Real

namespace CIO
variable {d : ℕ}

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

lemma vecAngle_nonneg (c chat : E d) : 0 ≤ vecAngle c chat := by
  unfold vecAngle; split_ifs
  · exact le_rfl
  · exact Real.arccos_nonneg _

lemma vecAngle_le_pi (c chat : E d) : vecAngle c chat ≤ π := by
  unfold vecAngle; split_ifs
  · exact Real.pi_pos.le
  · exact Real.arccos_le_pi _

lemma norm_of_mem (x : E d) (hx : x ∈ unitSphere d) : ‖x‖ = 1 := by
  simpa [unitSphere] using hx

lemma vecAngle_unit (c chat : E d) (hc : c ≠ 0) (hu : ‖chat‖ = 1) :
    vecAngle c chat = Real.arccos (inner ℝ c chat / ‖c‖) := by
  unfold vecAngle
  have : chat ≠ 0 := by intro h; rw [h] at hu; simp at hu
  rw [if_neg (by tauto), hu, mul_one]

lemma continuous_vecAngle (c : E d) :
    Continuous (fun chat : unitSphere d => vecAngle c (chat : E d)) := by
  by_cases hc : c = 0
  · have : (fun chat : unitSphere d => vecAngle c (chat : E d)) = fun _ => 0 := by
      funext chat; simp [vecAngle, hc]
    rw [this]; exact continuous_const
  · have : (fun chat : unitSphere d => vecAngle c (chat : E d)) =
        fun chat : unitSphere d => Real.arccos (inner ℝ c (chat : E d) / ‖c‖) := by
      funext chat; exact vecAngle_unit c chat hc (norm_of_mem _ chat.2)
    rw [this]
    exact Real.continuous_arccos.comp ((continuous_const.inner continuous_subtype_val).div_const _)

lemma bdd_sup (C : Set (E d)) (chat : E d) :
    BddAbove (Set.range fun c : C => vecAngle (c : E d) chat) :=
  ⟨π, by rintro _ ⟨c, rfl⟩; exact vecAngle_le_pi _ _⟩

lemma supF_nonneg (C : Set (E d)) (chat : E d) : 0 ≤ ⨆ c : C, vecAngle (c : E d) chat :=
  Real.iSup_nonneg (fun _ => vecAngle_nonneg _ _)

lemma bddBelow_F (C : Set (E d)) :
    BddBelow (Set.range fun chat : unitSphere d => ⨆ c : C, vecAngle (c : E d) (chat : E d)) :=
  ⟨0, by rintro _ ⟨y, rfl⟩; exact supF_nonneg C _⟩

lemma exists_circ (hd : 2 ≤ d) (C : Set (E d)) : ∃ chat, IsCircumcenter C chat := by
  haveI : Nonempty (unitSphere d) :=
    ⟨⟨EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ), by simp [unitSphere]⟩⟩
  haveI : CompactSpace (unitSphere d) := isCompact_iff_compactSpace.1 (isCompact_sphere 0 1)
  let F : unitSphere d → ℝ := fun chat => ⨆ c : C, vecAngle (c : E d) (chat : E d)
  have hlsc : LowerSemicontinuous F :=
    lowerSemicontinuous_ciSup (fun chat => bdd_sup C chat)
      (fun c => (continuous_vecAngle (c : E d)).lowerSemicontinuous)
  obtain ⟨x, -, hx⟩ := (hlsc.lowerSemicontinuousOn Set.univ).exists_isMinOn Set.univ_nonempty
    isCompact_univ
  rw [isMinOn_iff] at hx
  refine ⟨x, x.2, ?_⟩
  unfold uncAngle
  apply le_antisymm
  · exact le_ciInf (fun y => hx y (Set.mem_univ y))
  · exact ciInf_le (bddBelow_F C) x

lemma key_ineq (C : Set (E d)) (ci : E d) (hci : IsCircumcenter C ci) (c : E d) (hc : c ∈ C)
    (hc0 : c ≠ 0) : cos (uncAngle C) * ‖c‖ ≤ inner ℝ c ci := by
  have hn : ‖ci‖ = 1 := norm_of_mem _ hci.1
  have hα0 : 0 ≤ uncAngle C := by rw [← hci.2]; exact supF_nonneg C ci
  have hαπ : uncAngle C ≤ π := by
    haveI : Nonempty C := ⟨⟨c, hc⟩⟩
    rw [← hci.2]; exact ciSup_le (fun c => vecAngle_le_pi _ _)
  have hle : vecAngle c ci ≤ uncAngle C := by
    rw [← hci.2]; exact le_ciSup (bdd_sup C ci) ⟨c, hc⟩
  rw [vecAngle_unit c ci hc0 hn] at hle
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hcs := abs_real_inner_le_norm c ci
  rw [hn, mul_one] at hcs
  have ht1 : inner ℝ c ci / ‖c‖ ≤ 1 := by
    rw [div_le_one hcpos]; exact (le_abs_self _).trans hcs
  have ht2 : -1 ≤ inner ℝ c ci / ‖c‖ := by
    rw [le_div_iff₀ hcpos]; have := neg_abs_le (inner ℝ c ci); linarith
  have : cos (uncAngle C) ≤ inner ℝ c ci / ‖c‖ := by
    calc cos (uncAngle C) ≤ cos (Real.arccos (inner ℝ c ci / ‖c‖)) :=
          Real.cos_le_cos_of_nonneg_of_le_pi (Real.arccos_nonneg _) hαπ hle
      _ = _ := Real.cos_arccos ht2 ht1
  rwa [le_div_iff₀ hcpos] at this

lemma unique_circ (C : Set (E d)) (hC : C.Nonempty) (hC0 : (C \ {0}).Nonempty)
    (hα : uncAngle C < π / 2) (c1 c2 : E d) (h1 : IsCircumcenter C c1)
    (h2 : IsCircumcenter C c2) : c1 = c2 := by
  by_contra hne
  obtain ⟨c0, hc0C, hc00⟩ := hC0
  have hc00' : c0 ≠ 0 := hc00
  have hα0 : 0 ≤ uncAngle C := by rw [← h1.2]; exact supF_nonneg C c1
  have hαπ : uncAngle C ≤ π := by
    haveI : Nonempty C := hC.to_subtype
    rw [← h1.2]; exact ciSup_le (fun c => vecAngle_le_pi _ _)
  set α := uncAngle C with hαdef
  have hcos : 0 < cos α := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hα⟩
  have hn1 : ‖c1‖ = 1 := norm_of_mem _ h1.1
  have hn2 : ‖c2‖ = 1 := norm_of_mem _ h2.1
  have hc0pos : 0 < ‖c0‖ := norm_pos_iff.2 hc00'
  have k1 := key_ineq C c1 h1 c0 hc0C hc00'
  have k2 := key_ineq C c2 h2 c0 hc0C hc00'
  set s := c1 + c2 with hs
  have hinner : 2 * cos α * ‖c0‖ ≤ inner ℝ c0 s := by
    rw [hs, inner_add_right]; linarith
  have hspos : 0 < ‖s‖ := by
    rw [norm_pos_iff]; intro h0
    rw [h0, inner_zero_right] at hinner
    have : 0 < 2 * cos α * ‖c0‖ := by positivity
    linarith
  have hlt2 : ‖s‖ < 2 := by
    have hpar := parallelogram_law_with_norm ℝ c1 c2
    have hdiff : 0 < ‖c1 - c2‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    rw [hn1, hn2] at hpar
    rw [← hs] at hpar
    nlinarith
  set m : E d := ‖s‖⁻¹ • s with hm
  have hmn : ‖m‖ = 1 := by
    rw [hm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hspos.ne']
  have hmS : m ∈ unitSphere d := by simp [unitSphere, hmn]
  set κ : ℝ := 2 * cos α / ‖s‖ with hκ
  have hinner_m : ∀ c : E d, c ∈ C → c ≠ 0 → κ ≤ inner ℝ c m / ‖c‖ := by
    intro c hc hc0
    have hcp : 0 < ‖c‖ := norm_pos_iff.2 hc0
    have k1 := key_ineq C c1 h1 c hc hc0
    have k2 := key_ineq C c2 h2 c hc hc0
    have : 2 * cos α * ‖c‖ ≤ inner ℝ c s := by rw [hs, inner_add_right]; linarith
    rw [hm, inner_smul_right, hκ, le_div_iff₀ hcp]
    rw [div_mul_eq_mul_div, div_le_iff₀ hspos]
    calc 2 * cos α * ‖c‖ ≤ inner ℝ c s := this
      _ = ‖s‖⁻¹ * inner ℝ c s * ‖s‖ := by field_simp
  have hκ1 : κ ≤ 1 := by
    have := hinner_m c0 hc0C hc00'
    have hcs := abs_real_inner_le_norm c0 m
    rw [hmn, mul_one] at hcs
    have : inner ℝ c0 m / ‖c0‖ ≤ 1 := by
      rw [div_le_one hc0pos]; exact (le_abs_self _).trans hcs
    linarith
  have hκgt : cos α < κ := by
    rw [hκ, lt_div_iff₀ hspos]; nlinarith
  have hbound : ∀ c : C, vecAngle (c : E d) m ≤ Real.arccos κ := by
    intro ⟨c, hc⟩
    by_cases hc0 : c = 0
    · simp only [vecAngle, hc0]; simp [Real.arccos_nonneg]
    · show vecAngle c m ≤ _
      rw [vecAngle_unit c m hc0 hmn]
      exact Real.arccos_le_arccos (hinner_m c hc hc0)
  have hFm : (⨆ c : C, vecAngle (c : E d) m) ≤ Real.arccos κ := by
    haveI : Nonempty C := hC.to_subtype
    exact ciSup_le hbound
  have hα_le : α ≤ ⨆ c : C, vecAngle (c : E d) m := by
    have := ciInf_le (bddBelow_F C) (⟨m, hmS⟩ : unitSphere d)
    exact this
  have hlt : Real.arccos κ < α := by
    have := Real.arccos_lt_arccos (x := cos α) (y := κ) (by linarith [Real.neg_one_le_cos α])
      hκgt hκ1
    rwa [Real.arccos_cos hα0 hαπ] at this
  linarith

end CIO

open CIO in
theorem solution {d : ℕ} (hd : 2 ≤ d)
    (C : Set (EuclideanSpace ℝ (Fin d))) (hC : C.Nonempty) :
    (∃ chat, IsCircumcenter C chat) ∧
      ((C \ {0}).Nonempty → uncAngle C < Real.pi / 2 →
        ∀ c₁ c₂, IsCircumcenter C c₁ → IsCircumcenter C c₂ → c₁ = c₂) :=
  ⟨exists_circ hd C, fun h0 hα c₁ c₂ h1 h2 => unique_circ C hC h0 hα c₁ c₂ h1 h2⟩
