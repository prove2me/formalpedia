-- Prove2me | solution 1 for BregmanPPA.IneqMult.lemmaA1
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-07T19:49:49.155975+00:00
-- url     : https://prove2.me/submissions/e2974ef9-86ac-4511-aeb5-4e4c16e67939

import Definitions.Def_BregmanPPA_IneqMult_Program
set_option autoImplicit false
set_option autoImplicit false
open Filter Topology InertialFB.IFB BregmanPPA.IneqMult

/-- Lemma A1, p. 223: no nonzero nonnegative recession direction of the conjugate. -/
theorem solution {m : ℕ} (F : E m → EReal)
    (hproper : IsProperFn F) (hconvex : IsConvexFn F)
    (hclosed : LowerSemicontinuous F)
    (hu : ∃ u : E m, u ∈ posOrthant m ∧ F u ≠ ⊤ ∧
      ∃ v : E m, IsSubgradient F u v) :
    ∀ y : E m, y ∈ nonnegOrthant m → y ≠ 0 →
      ¬ IsRecessionDirection (conjE F) y := by
  obtain ⟨u,hu,hut,v,hv⟩ := hu
  have eu := EReal.coe_toReal hut (hproper.1 u)
  have hcv : conjE F v ≤ (((inner ℝ u v-(F u).toReal : ℝ)) : EReal) := by
    apply iSup_le
    intro q
    by_cases hqt : F q=⊤
    · simp only [hqt,EReal.sub_top]; exact bot_le
    have eq := EReal.coe_toReal hqt (hproper.1 q)
    have hi := hv.2 q
    rw [← eu,← eq,← EReal.coe_add] at hi
    have hir := EReal.coe_le_coe_iff.mp hi
    rw [← eq,← EReal.coe_sub]
    apply EReal.coe_le_coe_iff.mpr
    simp only [inner_sub_right] at hir
    have hqv : inner ℝ v q=inner ℝ q v := real_inner_comm _ _
    have huv : inner ℝ v u=inner ℝ u v := real_inner_comm _ _
    rw [hqv,huv] at hir
    linarith
  have hcvt : conjE F v ≠ ⊤ := ne_of_lt (hcv.trans_lt (EReal.coe_lt_top _))
  intro y hy hyne hrec
  have hpos : ∃ i, 0 < y i := by
    by_contra hn
    simp only [not_exists,not_lt] at hn
    apply hyne
    ext i
    exact le_antisymm (hn i) (hy i)
  have hinner : 0 < inner ℝ u y := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply,conj_trivial]
    obtain ⟨i,hi⟩ := hpos
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg (hy j) (hu j).le
    · exact ⟨i,Finset.mem_univ _,mul_pos hi (hu i)⟩
  let r : ℝ → ℝ := fun α => α*inner ℝ u y+(inner ℝ u v-(F u).toReal)
  have hr : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_id.atTop_mul_const hinner)
  have he : Tendsto (fun α => (r α : EReal)) atTop (𝓝 ⊤) := EReal.tendsto_coe_atTop.comp hr
  have hb (α : ℝ) : (r α : EReal) ≤ conjE F (v+α • y) := by
    have hi : ((inner ℝ u (v+α • y) : ℝ) : EReal)-F u ≤ conjE F (v+α • y) := le_iSup (fun q => ((inner ℝ q (v+α • y) : ℝ) : EReal)-F q) u
    rw [← eu,← EReal.coe_sub] at hi
    convert hi using 1
    congr 1
    simp only [r,inner_add_right,inner_smul_right]
    ring
  have ht : Tendsto (fun α : ℝ => conjE F (v+α • y)) atTop (𝓝 ⊤) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le he tendsto_const_nhds hb (fun _ => le_top)
  have hl := hrec v hcvt
  rw [ht.liminf_eq] at hl
  exact lt_irrefl _ hl




#print axioms solution
