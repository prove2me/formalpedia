-- Prove2me | solution 1 for BertsekasShreve.Contraction.minimax_assumption_C
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:35:15.887714+00:00
-- url     : https://prove2.me/submissions/c476e3f2-3388-4ae4-be0c-9630064b9c3b

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

open Filter Topology

namespace BertsekasShreve.Contraction

lemma mm_ereal_bounds (t : EReal) (L U : ℝ) (h1 : (L : EReal) ≤ t) (h2 : t ≤ (U : EReal)) :
    t = ((t.toReal : ℝ) : EReal) ∧ L ≤ t.toReal ∧ t.toReal ≤ U := by
  have hb : t ≠ ⊥ := fun h => by rw [h] at h1; exact absurd h1 (by simp)
  have ht : t ≠ ⊤ := fun h => by rw [h] at h2; exact absurd h2 (by simp)
  have e : ((t.toReal : ℝ) : EReal) = t := EReal.coe_toReal ht hb
  refine ⟨e.symm, ?_, ?_⟩
  · rw [← e] at h1; exact EReal.coe_le_coe_iff.1 h1
  · rw [← e] at h2; exact EReal.coe_le_coe_iff.1 h2

lemma mm_mkB {S : Type*} (f : S → ℝ) (M : ℝ) (h : ∀ x, |f x| ≤ M) :
    ∃ K : BFun S, ∀ x, K x = f x := by
  have hm : Memℓp (fun x => f x) ⊤ := by
    rw [memℓp_infty_iff]
    exact ⟨M, by rintro _ ⟨x, rfl⟩; simpa [Real.norm_eq_abs] using h x⟩
  exact ⟨⟨f, hm⟩, fun x => rfl⟩

lemma mm_abs_le_norm {S : Type*} (J : BFun S) (x : S) : |J x| ≤ ‖J‖ := by
  have := lp.norm_apply_le_norm (p := ⊤) (by simp) J x
  simpa [Real.norm_eq_abs] using this

lemma mm_abs_sub_le_norm {S : Type*} (A B : BFun S) (x : S) : |A x - B x| ≤ ‖A - B‖ := by
  have := lp.norm_apply_le_norm (p := ⊤) (by simp) (A - B) x
  simpa [Real.norm_eq_abs] using this

section
variable {S C W : Type*} (P : Model S C) (Wset : S → C → Set W)
    (hW : ∀ x, ∀ u ∈ P.U x, (Wset x u).Nonempty) (g : S → C → W → EReal) (f : S → C → W → S)
    (α : ℝ) (hα0 : 0 < α)
    (hH : ∀ (x : S) (u : C) (J : S → EReal),
      P.H x u J = ⨆ w ∈ Wset x u, (g x u w + (α : EReal) * J (f x u w)))
    (b : ℝ)
    (hg : ∀ x, ∀ u ∈ P.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ (b : EReal))

include hW hα0 hH hg in
lemma mm_val (x : S) (u : C) (hu : u ∈ P.U x) (J : BFun S) :
    ∃ r : ℝ, P.H x u (toF J) = (r : EReal) ∧
      (∀ w ∈ Wset x u, (g x u w).toReal + α * J (f x u w) ≤ r) ∧
      (∀ c : ℝ, (∀ w ∈ Wset x u, (g x u w).toReal + α * J (f x u w) ≤ c) → r ≤ c) ∧
      -(α * ‖J‖) ≤ r ∧ r ≤ b + α * ‖J‖ := by
  have hG : ∀ w, g x u w = (((g x u w).toReal : ℝ) : EReal) := by
    intro w
    exact (mm_ereal_bounds (g x u w) 0 b (by simpa using (hg x u hu w).1) (hg x u hu w).2).1
  have hGb : ∀ w, 0 ≤ (g x u w).toReal ∧ (g x u w).toReal ≤ b := by
    intro w
    exact (mm_ereal_bounds (g x u w) 0 b (by simpa using (hg x u hu w).1) (hg x u hu w).2).2
  have hterm : ∀ w, g x u w + (α : EReal) * toF J (f x u w) =
      (((g x u w).toReal + α * J (f x u w) : ℝ) : EReal) := by
    intro w
    rw [hG w, EReal.coe_add, EReal.coe_mul]
    simp [toF]
  set φ : W → ℝ := fun w => (g x u w).toReal + α * J (f x u w) with hφ
  have hs : P.H x u (toF J) = ⨆ w ∈ Wset x u, ((φ w : ℝ) : EReal) := by
    rw [hH]; simp_rw [hterm]; rfl
  have hφb : ∀ w, -(α * ‖J‖) ≤ φ w ∧ φ w ≤ b + α * ‖J‖ := by
    intro w
    have h1 := abs_le.1 (mm_abs_le_norm J (f x u w))
    have h2 := hGb w
    constructor
    · show _ ≤ (g x u w).toReal + α * J (f x u w)
      nlinarith
    · show (g x u w).toReal + α * J (f x u w) ≤ _
      nlinarith
  obtain ⟨w0, hw0⟩ := hW x u hu
  have hup : (⨆ w ∈ Wset x u, ((φ w : ℝ) : EReal)) ≤ ((b + α * ‖J‖ : ℝ) : EReal) :=
    iSup₂_le fun w _ => EReal.coe_le_coe_iff.2 (hφb w).2
  have hlo : ((-(α * ‖J‖) : ℝ) : EReal) ≤ ⨆ w ∈ Wset x u, ((φ w : ℝ) : EReal) :=
    le_iSup₂_of_le w0 hw0 (EReal.coe_le_coe_iff.2 (hφb w0).1)
  obtain ⟨e, h1, h2⟩ := mm_ereal_bounds _ _ _ hlo hup
  refine ⟨_, hs.trans e, ?_, ?_, h1, h2⟩
  · intro w hw
    have : ((φ w : ℝ) : EReal) ≤ ⨆ w ∈ Wset x u, ((φ w : ℝ) : EReal) := le_iSup₂_of_le w hw le_rfl
    rw [e] at this
    exact EReal.coe_le_coe_iff.1 this
  · intro c hc
    have : (⨆ w ∈ Wset x u, ((φ w : ℝ) : EReal)) ≤ (c : EReal) :=
      iSup₂_le fun w hw => EReal.coe_le_coe_iff.2 (hc w hw)
    rw [e] at this
    exact EReal.coe_le_coe_iff.1 this

include hW hα0 hH hg in
lemma mm_lip (x : S) (u : C) (hu : u ∈ P.U x) (J J' : BFun S) :
    ∃ a b' : ℝ, P.H x u (toF J) = (a : EReal) ∧ P.H x u (toF J') = (b' : EReal) ∧
      |a - b'| ≤ α * ‖J - J'‖ := by
  obtain ⟨r, hr, hub, hlub, -, -⟩ := mm_val P Wset hW g f α hα0 hH b hg x u hu J
  obtain ⟨r', hr', hub', hlub', -, -⟩ := mm_val P Wset hW g f α hα0 hH b hg x u hu J'
  refine ⟨r, r', hr, hr', abs_le.2 ⟨?_, ?_⟩⟩
  · have : r' ≤ r + α * ‖J - J'‖ := by
      apply hlub'
      intro w hw
      have h1 := hub w hw
      have h2 := (abs_le.1 (mm_abs_sub_le_norm J J' (f x u w)))
      nlinarith
    linarith
  · have : r ≤ r' + α * ‖J - J'‖ := by
      apply hlub
      intro w hw
      have h1 := hub' w hw
      have h2 := (abs_le.1 (mm_abs_sub_le_norm J J' (f x u w)))
      nlinarith
    linarith

end

theorem minimax_core {S C W : Type*} (P : Model S C) (Wset : S → C → Set W)
    (hW : ∀ x, ∀ u ∈ P.U x, (Wset x u).Nonempty) (g : S → C → W → EReal) (f : S → C → W → S)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hH : ∀ (x : S) (u : C) (J : S → EReal),
      P.H x u J = ⨆ w ∈ Wset x u, (g x u w + (α : EReal) * J (f x u w)))
    (hJ0 : P.J0 = fun _ => 0) (b : ℝ)
    (hg : ∀ x, ∀ u ∈ P.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ (b : EReal)) :
    AssumptionC P Set.univ 1 α α := by
  have hlip : ∀ (μ : P.Selector) (J J' : BFun S),
      SupDistLe (P.Tmu μ (toF J)) (P.Tmu μ (toF J')) (α * ‖J - J'‖) := by
    intro μ J J' x
    exact mm_lip P Wset hW g f α hα0 hH b hg x (μ.1 x) (μ.2 x) J J'
  -- Tmu monotone on all EReal functions
  have hTmono : ∀ (μ : P.Selector) (J J' : S → EReal), J ≤ J' → P.Tmu μ J ≤ P.Tmu μ J' :=
    fun μ J J' h x => P.mono x (μ.1 x) (μ.2 x) J J' h
  have hcomp_mono : ∀ (π : P.Policy) N (J J' : S → EReal), J ≤ J' → P.comp π N J ≤ P.comp π N J' := by
    intro π N; induction N with
    | zero => intro J J' h; exact h
    | succ N ih => intro J J' h; exact ih _ _ (hTmono _ J J' h)
  set c : ℝ := b / (1 - α) with hc
  have hcα : b + α * c = c := by
    rw [hc]; field_simp [show (1 - α) ≠ 0 by linarith]; ring
  have hTc : ∀ (μ : P.Selector) (J : S → EReal), J ≤ (fun _ => (c : EReal)) →
      P.Tmu μ J ≤ (fun _ => (c : EReal)) := by
    intro μ J hJ x
    refine (hTmono μ J _ hJ x).trans ?_
    show P.H x (μ.1 x) (fun _ => (c : EReal)) ≤ _
    rw [hH]
    apply iSup₂_le
    intro w _
    obtain ⟨hg0, hgb⟩ := hg x (μ.1 x) (μ.2 x) w
    have e : (α : EReal) * (c : EReal) = ((α * c : ℝ) : EReal) := by rw [EReal.coe_mul]
    rw [e]
    calc g x (μ.1 x) w + ((α * c : ℝ) : EReal) ≤ (b : EReal) + ((α * c : ℝ) : EReal) :=
          add_le_add_left hgb _
      _ = (c : EReal) := by rw [← EReal.coe_add, hcα]
  have hcomp_c : ∀ (π : P.Policy) N (J : S → EReal), J ≤ (fun _ => (c : EReal)) →
      P.comp π N J ≤ (fun _ => (c : EReal)) := by
    intro π N; induction N with
    | zero => intro J h; exact h
    | succ N ih => intro J h; exact ih _ (hTc _ J h)
  have hT0 : ∀ μ : P.Selector, P.J0 ≤ P.Tmu μ P.J0 := by
    intro μ x
    rw [hJ0]
    show (0 : EReal) ≤ P.H x (μ.1 x) (fun _ => 0)
    rw [hH]
    obtain ⟨w0, hw0⟩ := hW x (μ.1 x) (μ.2 x)
    refine le_iSup₂_of_le w0 hw0 ?_
    simpa using (hg x (μ.1 x) (μ.2 x) w0).1
  have hJ0c : P.J0 ≤ (fun _ => (c : EReal)) := by
    intro x
    rw [hJ0]
    obtain ⟨u0, hu0⟩ := P.U_nonempty x
    obtain ⟨w0, -⟩ := hW x u0 hu0
    obtain ⟨h1, h2⟩ := hg x u0 hu0 w0
    have hb : (0 : EReal) ≤ (b : EReal) := h1.trans h2
    have hb' : 0 ≤ b := by exact_mod_cast hb
    have hc0 : 0 ≤ c := div_nonneg hb' (by linarith)
    show (0 : EReal) ≤ (c : EReal)
    exact_mod_cast hc0
  have hbd : ∀ J : BFun S, ∀ x, ∀ u ∈ P.U x, ∃ r : ℝ, P.H x u (toF J) = (r : EReal) ∧
      -(α * ‖J‖) ≤ r ∧ r ≤ b + α * ‖J‖ := by
    intro J x u hu
    obtain ⟨r, hr, -, -, h1, h2⟩ := mm_val P Wset hW g f α hα0 hH b hg x u hu J
    exact ⟨r, hr, h1, h2⟩
  refine
    { isClosed := isClosed_univ
      J0_mem := ⟨0, trivial, by rw [hJ0]; funext x; simp [toF]⟩
      T_mem := ?_
      Tmu_mem := ?_
      limit_real := ?_
      m_pos := one_pos
      ρ_pos := hα0
      ρ_lt_one := hα1
      α_pos := hα0
      lipschitz := hlip
      contraction := ?_ }
  · intro J _
    have key : ∀ x, P.T (toF J) x = (((P.T (toF J) x).toReal : ℝ) : EReal) ∧
        -(α * ‖J‖) ≤ (P.T (toF J) x).toReal ∧ (P.T (toF J) x).toReal ≤ b + α * ‖J‖ := by
      intro x
      apply mm_ereal_bounds
      · apply le_iInf₂
        intro u hu
        obtain ⟨r, hr, h1, -⟩ := hbd J x u hu
        rw [hr]; exact EReal.coe_le_coe_iff.2 h1
      · obtain ⟨u0, hu0⟩ := P.U_nonempty x
        refine (iInf₂_le u0 hu0).trans ?_
        obtain ⟨r, hr, -, h2⟩ := hbd J x u0 hu0
        rw [hr]; exact EReal.coe_le_coe_iff.2 h2
    obtain ⟨K, hK⟩ := mm_mkB (fun x => (P.T (toF J) x).toReal) (|b| + α * ‖J‖) (fun x =>
      abs_le.2 ⟨by linarith [(key x).2.1, abs_nonneg b], by linarith [(key x).2.2, le_abs_self b]⟩)
    refine ⟨K, trivial, funext fun x => ?_⟩
    rw [(key x).1]
    show _ = ((K x : ℝ) : EReal)
    rw [hK x]
  · intro μ J _
    obtain ⟨r, hr⟩ : ∃ r : S → ℝ, ∀ x, P.Tmu μ (toF J) x = (r x : EReal) ∧
        -(α * ‖J‖) ≤ r x ∧ r x ≤ b + α * ‖J‖ := by
      choose r hr using fun x => hbd J x (μ.1 x) (μ.2 x)
      exact ⟨r, hr⟩
    obtain ⟨K, hK⟩ := mm_mkB r (|b| + α * ‖J‖) (fun x =>
      abs_le.2 ⟨by linarith [(hr x).2.1, abs_nonneg b], by linarith [(hr x).2.2, le_abs_self b]⟩)
    refine ⟨K, trivial, funext fun x => ?_⟩
    rw [(hr x).1]
    show _ = ((K x : ℝ) : EReal)
    rw [hK x]
  · intro π x
    have hmono : Monotone (fun N => P.comp π N P.J0 x) := by
      apply monotone_nat_of_le_succ
      intro N
      show P.comp π N P.J0 x ≤ P.comp π N (P.Tmu (π N) P.J0) x
      exact hcomp_mono π N _ _ (hT0 (π N)) x
    have hlo : ((0 : ℝ) : EReal) ≤ ⨆ N, P.comp π N P.J0 x := by
      refine le_iSup_of_le 0 ?_
      show ((0 : ℝ) : EReal) ≤ P.J0 x
      rw [hJ0]; simp
    have hup : (⨆ N, P.comp π N P.J0 x) ≤ (c : EReal) :=
      iSup_le fun N => hcomp_c π N P.J0 hJ0c x
    obtain ⟨e, -, -⟩ := mm_ereal_bounds _ _ _ hlo hup
    refine ⟨(⨆ N, P.comp π N P.J0 x).toReal, ?_⟩
    rw [← e]
    exact tendsto_atTop_iSup hmono
  · intro π J _ J' _
    exact hlip (π 0) J J'

end BertsekasShreve.Contraction

open BertsekasShreve.Contraction


theorem solution {S C W : Type*} (P : Model S C) (Wset : S → C → Set W)
    (hW : ∀ x, ∀ u ∈ P.U x, (Wset x u).Nonempty) (g : S → C → W → EReal) (f : S → C → W → S)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hH : ∀ (x : S) (u : C) (J : S → EReal),
      P.H x u J = ⨆ w ∈ Wset x u, (g x u w + (α : EReal) * J (f x u w)))
    (hJ0 : P.J0 = fun _ => 0) (b : ℝ)
    (hg : ∀ x, ∀ u ∈ P.U x, ∀ w : W, 0 ≤ g x u w ∧ g x u w ≤ (b : EReal)) :
    AssumptionC P Set.univ 1 α α := by
  exact minimax_core P Wset hW g f α hα0 hα1 hH hJ0 b hg
