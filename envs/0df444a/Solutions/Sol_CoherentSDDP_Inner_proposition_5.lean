-- Prove2me | solution 1 for CoherentSDDP.Inner.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:10:06.420822+00:00
-- url     : https://prove2.me/submissions/1b8ac9c9-7586-4c23-b065-dc7b44e3fba9

import Mathlib
import Definitions.Def_CoherentSDDP_Inner_Basic
import Definitions.Def_CoherentSDDP_Inner_Model

namespace RRAux_CoherentSDDP_Inner_proposition_5

open CoherentSDDP.Inner

theorem coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem smul_ne_bot {w : ℝ} (hw : 0 ≤ w) {q : EReal} (hq : q ≠ ⊥) : ((w : ℝ) : EReal) * q ≠ ⊥ := by
  rcases hw.eq_or_lt with h | h
  · rw [← h]; simp
  · induction q using EReal.rec with
    | bot => exact absurd rfl hq
    | top => rw [EReal.coe_mul_top_of_pos h]; exact (by decide : (⊤ : EReal) ≠ ⊥)
    | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

theorem sum_ne_bot {ι : Type*} (s : Finset ι) (f : ι → EReal) (hf : ∀ i ∈ s, f i ≠ ⊥) :
    ∑ i ∈ s, f i ≠ ⊥ :=
  Finset.sum_induction f (· ≠ ⊥) (fun a b ha hb => EReal.add_ne_bot_iff.2 ⟨ha, hb⟩)
    (by simp) hf

theorem esum_real {J : ℕ} (w : Fin J → ℝ) (hw : ∀ j, 0 ≤ w j) (q : Fin J → EReal)
    (hq : ∀ j, q j ≠ ⊥) (htop : ∀ j, 0 < w j → q j ≠ ⊤) :
    ∑ j, ((w j : ℝ) : EReal) * q j = ((∑ j, w j * (q j).toReal : ℝ) : EReal) := by
  rw [coe_sum]
  apply Finset.sum_congr rfl
  intro j _
  rcases (hw j).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [EReal.coe_mul, EReal.coe_toReal (htop j h) (hq j)]

theorem esum_top {J : ℕ} (w : Fin J → ℝ) (hw : ∀ j, 0 ≤ w j) (q : Fin J → EReal)
    (hq : ∀ j, q j ≠ ⊥) (j : Fin J) (hj : 0 < w j) (hqj : q j = ⊤) :
    ∑ j, ((w j : ℝ) : EReal) * q j = ⊤ := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hqj, EReal.coe_mul_top_of_pos hj]
  exact EReal.top_add_of_ne_bot
    (sum_ne_bot _ _ (fun i _ => smul_ne_bot (hw i) (hq i)))

theorem le_coe_of_forall {X : EReal} {a : ℝ} (h : ∀ ε : ℝ, 0 < ε → X ≤ ((a + ε : ℝ) : EReal)) :
    X ≤ (a : EReal) := by
  induction X using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd (top_le_iff.1 (h 1 one_pos)) (EReal.coe_ne_top _)
  | coe r =>
    rw [EReal.coe_le_coe_iff]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    exact EReal.coe_le_coe_iff.1 (h ε hε)

theorem toReal_le_of_le_coe {X : EReal} {a : ℝ} (hX : X ≠ ⊥) (h : X ≤ (a : EReal)) :
    X.toReal ≤ a := by
  have := EReal.toReal_le_toReal h hX (EReal.coe_ne_top a)
  rwa [EReal.toReal_coe] at this

theorem riskE_le_coe {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) (hmono : RiskMonotone ρ) (Z : Ω → EReal)
    (G : Ω → ℝ) (hZ : ∀ ω, Z ω ≠ ⊥) (hle : ∀ ω, Z ω ≤ (G ω : EReal)) :
    riskE ρ Z ≤ ((ρ G : ℝ) : EReal) := by
  have hnt : ∀ ω, Z ω ≠ ⊤ := fun ω h => by
    have := hle ω; rw [h] at this; exact EReal.coe_ne_top _ (top_le_iff.1 this)
  rw [riskE, if_pos hnt, EReal.coe_le_coe_iff]
  exact hmono _ _ fun ω => toReal_le_of_le_coe (hZ ω) (hle ω)

theorem riskE_ne_bot {Ω : Type*} (ρ : (Ω → ℝ) → ℝ) (Z : Ω → EReal) : riskE ρ Z ≠ ⊥ := by
  unfold riskE
  split_ifs
  · exact EReal.coe_ne_bot _
  · exact (by decide : (⊤ : EReal) ≠ ⊥)

variable {n m : ℕ} {Ω : ℕ → Type}

def CvxE (f : (Fin n → ℝ) → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∀ (J : ℕ) (w : Fin J → ℝ) (xs : Fin J → Fin n → ℝ), (∀ j, 0 ≤ w j) →
    ∑ j, w j = 1 → (∀ j, 0 < w j → f (xs j) ≠ ⊤) →
    f (∑ j, w j • xs j) ≤ ((∑ j, w j * (f (xs j)).toReal : ℝ) : EReal)

theorem min_le_mul (w r : ℝ) (h0 : 0 ≤ w) (h1 : w ≤ 1) : min r 0 ≤ w * r := by
  rcases le_total r 0 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; positivity

theorem Qhat_cvx_top (M : Model n m Ω) (D : InnerData n) (s : ℕ) (hs : M.T < s) :
    CvxE (Qhat M D s) := by
  refine ⟨fun x => ?_, fun J w xs _ _ _ => ?_⟩
  · rw [Qhat, if_pos hs]; simp
  · simp only [Qhat, if_pos hs, EReal.toReal_zero, mul_zero, Finset.sum_const_zero,
      EReal.coe_zero, le_refl]

theorem Qhat_unfold (M : Model n m Ω) (D : InnerData n) (s : ℕ) (hs : s ≤ M.T)
    (x : Fin n → ℝ) : Qhat M D s x = ⨅ w ∈ stdSimplex ℝ (Fin (D.J s)),
      ⨅ (_ : ∑ j, w j • D.pts s j = x), ∑ j, ((w j : ℝ) : EReal) * D.qv s j := by
  rw [Qhat, if_neg (not_lt.2 hs)]

theorem Qhat_cvx (M : Model n m Ω) (D : InnerData n) (s : ℕ) (hs : s ≤ M.T)
    (hqv : ∀ j, D.qv s j ≠ ⊥) : CvxE (Qhat M D s) := by
  have hbot : ∀ x, Qhat M D s x ≠ ⊥ := by
   intro x
   ·
    have hL : ((∑ k, min (D.qv s k).toReal 0 : ℝ) : EReal) ≤ Qhat M D s x := by
      rw [Qhat_unfold M D s hs]
      refine le_iInf₂ fun μ hμ => le_iInf fun _ => ?_
      by_cases ht : ∃ k, 0 < μ k ∧ D.qv s k = ⊤
      · obtain ⟨k, hk, hkt⟩ := ht
        rw [esum_top μ hμ.1 _ hqv k hk hkt]; exact le_top
      · push Not at ht
        rw [esum_real μ hμ.1 _ hqv ht, EReal.coe_le_coe_iff]
        apply Finset.sum_le_sum
        intro k _
        apply min_le_mul _ _ (hμ.1 k)
        rw [← hμ.2]
        exact Finset.single_le_sum (fun i _ => hμ.1 i) (Finset.mem_univ k)
    intro h
    rw [h] at hL
    exact EReal.coe_ne_bot _ (le_bot_iff.1 hL)
  refine ⟨hbot, fun J w xs hw0 hw1 htop => ?_⟩
  · set a : Fin J → ℝ := fun j => (Qhat M D s (xs j)).toReal with ha
    apply le_coe_of_forall
    intro ε hε
    have hch : ∀ j, ∃ μ : Fin (D.J s) → ℝ, 0 < w j → (μ ∈ stdSimplex ℝ (Fin (D.J s)) ∧
        ∑ k, μ k • D.pts s k = xs j ∧ (∀ k, 0 < μ k → D.qv s k ≠ ⊤) ∧
        ∑ k, μ k * (D.qv s k).toReal < a j + ε) := by
      intro j
      by_cases hj : 0 < w j
      · have hb : Qhat M D s (xs j) ≠ ⊥ := hbot (xs j)
        have hlt : Qhat M D s (xs j) < ((a j + ε : ℝ) : EReal) := by
          rw [← EReal.coe_toReal (htop j hj) hb, EReal.coe_lt_coe_iff]
          simp only [ha]; linarith
        rw [Qhat_unfold M D s hs] at hlt
        obtain ⟨μ, hlt⟩ := iInf_lt_iff.1 hlt
        obtain ⟨hμ, hlt⟩ := iInf_lt_iff.1 hlt
        obtain ⟨hpt, hlt⟩ := iInf_lt_iff.1 hlt
        have hnt : ∀ k, 0 < μ k → D.qv s k ≠ ⊤ := by
          intro k hk hkt
          rw [esum_top μ hμ.1 _ hqv k hk hkt] at hlt
          exact (not_top_lt hlt)
        refine ⟨μ, fun _ => ⟨hμ, hpt, hnt, ?_⟩⟩
        rw [esum_real μ hμ.1 _ hqv hnt, EReal.coe_lt_coe_iff] at hlt
        exact hlt
      · exact ⟨0, fun h => absurd h hj⟩
    choose μ hμ using hch
    let lam : Fin (D.J s) → ℝ := fun k => ∑ j, w j * μ j k
    have hterm0 : ∀ j k, 0 ≤ w j * μ j k := by
      intro j k
      rcases (hw0 j).eq_or_lt with h | h
      · rw [← h, zero_mul]
      · exact mul_nonneg h.le ((hμ j h).1.1 k)
    have hlam : lam ∈ stdSimplex ℝ (Fin (D.J s)) := by
      refine ⟨fun k => Finset.sum_nonneg fun j _ => hterm0 j k, ?_⟩
      simp only [lam]
      rw [Finset.sum_comm]
      rw [← hw1]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum]
      rcases (hw0 j).eq_or_lt with h | h
      · rw [← h, zero_mul]
      · rw [(hμ j h).1.2, mul_one]
    have hpt : ∑ k, lam k • D.pts s k = ∑ j, w j • xs j := by
      simp only [lam, Finset.sum_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rcases (hw0 j).eq_or_lt with h | h
      · rw [← h]; simp
      · rw [← (hμ j h).2.1, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_smul]
    have hnt : ∀ k, 0 < lam k → D.qv s k ≠ ⊤ := by
      intro k hk
      obtain ⟨j, _, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ)
        (f := fun _ => (0 : ℝ)) (by simpa [lam] using hk)
      have hwj : 0 < w j := by
        rcases (hw0 j).eq_or_lt with h | h
        · rw [← h, zero_mul] at hj; exact absurd hj (lt_irrefl _)
        · exact h
      have hμk : 0 < μ j k := pos_of_mul_pos_right hj hwj.le
      exact (hμ j hwj).2.2.1 k hμk
    have hle : Qhat M D s (∑ j, w j • xs j) ≤ ∑ k, ((lam k : ℝ) : EReal) * D.qv s k := by
      rw [Qhat_unfold M D s hs]
      exact le_trans (iInf₂_le lam hlam) (iInf_le_of_le hpt le_rfl)
    refine le_trans hle ?_
    rw [esum_real lam hlam.1 _ hqv hnt, EReal.coe_le_coe_iff]
    simp only [lam, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∑ j, w j * (a j + ε) = ∑ j, w j * a j + ε := by
      rw [Finset.sum_congr rfl (fun j _ => mul_add (w j) (a j) ε), Finset.sum_add_distrib,
        ← Finset.sum_mul, hw1, one_mul]
    rw [← this]
    apply Finset.sum_le_sum
    intro j _
    rcases (hw0 j).eq_or_lt with h | h
    · rw [← h]; simp
    · have := (hμ j h).2.2.2
      have h2 : ∑ k, w j * μ j k * (D.qv s k).toReal = w j * ∑ k, μ j k * (D.qv s k).toReal := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left this.le h.le

open Matrix in
theorem qstage_cvx [∀ t, Fintype (Ω t)] (M : Model n m Ω) (D : InnerData n)
    (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ) (x1hat : Fin n → ℝ)
    (hπ : IsInnerPolicy M D xhat x1hat) (t : ℕ) (ht2 : 2 ≤ t) (htT : t ≤ M.T)
    (hQ : CvxE (Qhat M D (t + 1))) (ω : Ω t) : CvxE (fun x => qstage M D t x ω) := by
  have hbot : ∀ x, qstage M D t x ω ≠ ⊥ := by
    intro x
    by_cases hne : (M.feas t x ω).Nonempty
    · obtain ⟨hmem, hmin⟩ := hπ.1 t ht2 htT x ω hne
      have hle : ((M.c t ⬝ᵥ xhat t x ω : ℝ) : EReal) + Qhat M D (t + 1) (xhat t x ω) ≤
          qstage M D t x ω := le_iInf₂ fun x' hx' => hmin x' hx'
      intro h
      rw [h, le_bot_iff] at hle
      exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, hQ.1 _⟩ hle
    · have hle : (⊤ : EReal) ≤ qstage M D t x ω :=
        le_iInf₂ fun x' hx' => absurd ⟨x', hx'⟩ hne
      intro h; rw [h] at hle; exact absurd (le_bot_iff.1 hle) (by decide)
  refine ⟨hbot, fun J w xs hw0 hw1 htop => ?_⟩
  simp only at htop ⊢
  set a : Fin J → ℝ := fun j => (qstage M D t (xs j) ω).toReal with ha
  apply le_coe_of_forall
  intro ε hε
  have hch : ∀ j, ∃ x' : Fin n → ℝ, 0 < w j → (x' ∈ M.feas t (xs j) ω ∧
      Qhat M D (t + 1) x' ≠ ⊤ ∧
      M.c t ⬝ᵥ x' + (Qhat M D (t + 1) x').toReal < a j + ε) := by
    intro j
    by_cases hj : 0 < w j
    · have hlt : qstage M D t (xs j) ω < ((a j + ε : ℝ) : EReal) := by
        rw [← EReal.coe_toReal (htop j hj) (hbot (xs j)), EReal.coe_lt_coe_iff]
        simp only [ha]; linarith
      obtain ⟨x', hlt⟩ := iInf_lt_iff.1 hlt
      obtain ⟨hx', hlt⟩ := iInf_lt_iff.1 hlt
      have hnt : Qhat M D (t + 1) x' ≠ ⊤ := by
        intro h; rw [h, EReal.coe_add_top] at hlt; exact not_top_lt hlt
      refine ⟨x', fun _ => ⟨hx', hnt, ?_⟩⟩
      rw [← EReal.coe_toReal hnt (hQ.1 x'), ← EReal.coe_add, EReal.coe_lt_coe_iff] at hlt
      exact hlt
    · exact ⟨0, fun h => absurd h hj⟩
  choose xp hxp using hch
  let z : Fin n → ℝ := ∑ j, w j • xp j
  have hz : z ∈ M.feas t (∑ j, w j • xs j) ω := by
    refine ⟨Finset.sum_nonneg fun j _ => ?_, ?_⟩
    · rcases (hw0 j).eq_or_lt with h | h
      · rw [← h, zero_smul]
      · exact smul_nonneg h.le (hxp j h).1.1
    · simp only [z]
      rw [mulVec_sum, mulVec_sum]
      have : ∀ j, M.A t *ᵥ (w j • xp j) = w j • (M.b t ω - M.E t *ᵥ xs j) := by
        intro j
        rcases (hw0 j).eq_or_lt with h | h
        · rw [← h]; simp
        · rw [mulVec_smul, (hxp j h).1.2]
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      simp only [smul_sub, Finset.sum_sub_distrib, mulVec_smul]
      rw [← Finset.sum_smul, hw1, one_smul]
  have hQz := hQ.2 J w xp hw0 hw1 (fun j hj => (hxp j hj).2.1)
  have hle1 : qstage M D t (∑ j, w j • xs j) ω ≤
      ((M.c t ⬝ᵥ z : ℝ) : EReal) + Qhat M D (t + 1) z := iInf₂_le z hz
  refine le_trans hle1 (le_trans (add_le_add_right hQz _) ?_)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  simp only [z]
  rw [dotProduct_sum]
  simp only [dotProduct_smul, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  have : ∑ j, w j * (a j + ε) = ∑ j, w j * a j + ε := by
    rw [Finset.sum_congr rfl (fun j _ => mul_add (w j) (a j) ε), Finset.sum_add_distrib,
      ← Finset.sum_mul, hw1, one_mul]
  rw [← this]
  apply Finset.sum_le_sum
  intro j _
  rcases (hw0 j).eq_or_lt with h | h
  · rw [← h]; simp
  · rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hxp j h).2.2.le h.le

theorem rho_zero {Ω' : Type*} (ρ : (Ω' → ℝ) → ℝ) (hρ : IsCoherent ρ) : ρ 0 = 0 := by
  have h := hρ.2.2.1 2 0 two_pos
  rw [smul_zero] at h
  linarith

theorem rho_sum {Ω' : Type*} (ρ : (Ω' → ℝ) → ℝ) (hρ : IsCoherent ρ) {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (g : ι → Ω' → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ρ (∑ j ∈ s, w j • g j) ≤ ∑ j ∈ s, w j * ρ (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rho_zero ρ hρ]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    refine le_trans (hρ.1 _ _) (add_le_add ?_ ih)
    rcases (hw a).eq_or_lt with h | h
    · rw [← h, zero_smul, zero_mul, rho_zero ρ hρ]
    · rw [hρ.2.2.1 _ _ h]

theorem vhat_ne_bot (M : Model n m Ω) (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ)
    (t : ℕ) (x : Fin n → ℝ) (ω : Ω t) : vhat M xhat t x ω ≠ ⊥ := by
  rw [vhat.eq_1]
  split_ifs
  · exact EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _, riskE_ne_bot _ _⟩
  · rw [add_zero]; exact EReal.coe_ne_bot _
  · decide

open Matrix in
theorem vhat_le_qstage (M : Model n m Ω) (D : InnerData n)
    (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ) (x1hat : Fin n → ℝ)
    (hπ : IsInnerPolicy M D xhat x1hat) (t : ℕ) (ht2 : 2 ≤ t) (htT : t ≤ M.T)
    (IH : t < M.T → ∀ x, riskE (M.ρ (t + 1)) (fun ω => vhat M xhat (t + 1) x ω) ≤
      Qhat M D (t + 1) x) (x : Fin n → ℝ) (ω : Ω t) :
    vhat M xhat t x ω ≤ qstage M D t x ω := by
  rw [vhat.eq_1]
  split_ifs with hne h
  · obtain ⟨_, hmin⟩ := hπ.1 t ht2 htT x ω hne
    exact le_iInf₂ fun x' hx' => le_trans (add_le_add_right (IH h _) _) (hmin x' hx')
  · obtain ⟨_, hmin⟩ := hπ.1 t ht2 htT x ω hne
    have h0 : Qhat M D (t + 1) (xhat t x ω) = 0 := by
      rw [Qhat, if_pos (by omega)]
    refine le_iInf₂ fun x' hx' => le_trans ?_ (hmin x' hx')
    rw [h0]
  · exact le_iInf₂ fun x' hx' => absurd ⟨x', hx'⟩ hne

theorem claim [∀ t, Fintype (Ω t)] (M : Model n m Ω)
    (hρ : ∀ t, 2 ≤ t → t ≤ M.T → IsCoherent (M.ρ t))
    (D : InnerData n) (hD : UpperBounds M D)
    (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ) (x1hat : Fin n → ℝ)
    (hπ : IsInnerPolicy M D xhat x1hat) (t : ℕ) (ht2 : 2 ≤ t) (htT : t ≤ M.T)
    (IH : t < M.T → ∀ x, riskE (M.ρ (t + 1)) (fun ω => vhat M xhat (t + 1) x ω) ≤
      Qhat M D (t + 1) x) (x : Fin n → ℝ) :
    riskE (M.ρ t) (fun ω => vhat M xhat t x ω) ≤ Qhat M D t x := by
  have hqv : ∀ s, 2 ≤ s → s ≤ M.T → ∀ j, D.qv s j ≠ ⊥ := by
    intro s hs2 hsT j h
    have := hD s hs2 hsT j
    rw [h, le_bot_iff] at this
    exact riskE_ne_bot _ _ this
  have hQ : CvxE (Qhat M D (t + 1)) := by
    by_cases h : t + 1 ≤ M.T
    · exact Qhat_cvx M D (t + 1) h (hqv (t + 1) (by omega) h)
    · exact Qhat_cvx_top M D (t + 1) (by omega)
  rw [Qhat_unfold M D t htT]
  refine le_iInf₂ fun w hw => le_iInf fun hpt => ?_
  by_cases htp : ∃ j, 0 < w j ∧ D.qv t j = ⊤
  · obtain ⟨j, hj, hjt⟩ := htp
    rw [esum_top w hw.1 _ (hqv t ht2 htT) j hj hjt]; exact le_top
  push Not at htp
  rw [esum_real w hw.1 _ (hqv t ht2 htT) htp]
  have hUB : ∀ j, 0 < w j → (∀ ω, qstage M D t (D.pts t j) ω ≠ ⊤) ∧
      M.ρ t (fun ω => (qstage M D t (D.pts t j) ω).toReal) ≤ (D.qv t j).toReal := by
    intro j hj
    have h := hD t ht2 htT j
    by_cases hall : ∀ ω, qstage M D t (D.pts t j) ω ≠ ⊤
    · refine ⟨hall, ?_⟩
      rw [riskE, if_pos hall, ← EReal.coe_toReal (htp j hj) (hqv t ht2 htT j),
        EReal.coe_le_coe_iff] at h
      exact h
    · rw [riskE, if_neg hall, top_le_iff] at h
      exact absurd h (htp j hj)
  let G : Ω t → ℝ := fun ω => ∑ j, w j * (qstage M D t (D.pts t j) ω).toReal
  have hv : ∀ ω, vhat M xhat t x ω ≤ ((G ω : ℝ) : EReal) := by
    intro ω
    refine le_trans (vhat_le_qstage M D xhat x1hat hπ t ht2 htT IH x ω) ?_
    rw [← hpt]
    exact (qstage_cvx M D xhat x1hat hπ t ht2 htT hQ ω).2 _ w (D.pts t) hw.1 hw.2
      (fun j hj => (hUB j hj).1 ω)
  have hcoh := hρ t ht2 htT
  refine le_trans (riskE_le_coe _ hcoh.2.1 _ G (vhat_ne_bot M xhat t x) hv) ?_
  rw [EReal.coe_le_coe_iff]
  have hG : G = ∑ j, w j • (fun ω => (qstage M D t (D.pts t j) ω).toReal) := by
    funext ω
    simp only [G, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hG]
  refine le_trans (rho_sum _ hcoh Finset.univ w _ hw.1) (Finset.sum_le_sum fun j _ => ?_)
  rcases (hw.1 j).eq_or_lt with h | h
  · rw [← h, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (hUB j h).2 h.le

end RRAux_CoherentSDDP_Inner_proposition_5

open CoherentSDDP.Inner in
theorem solution {n m : ℕ} {Ω : ℕ → Type} [∀ t, Fintype (Ω t)] [∀ t, Nonempty (Ω t)]
    (M : Model n m Ω) (hT : 2 ≤ M.T) (hρ : ∀ t, 2 ≤ t → t ≤ M.T → IsCoherent (M.ρ t))
    (D : InnerData n) (hD : UpperBounds M D)
    (xhat : (t : ℕ) → (Fin n → ℝ) → Ω t → Fin n → ℝ) (x1hat : Fin n → ℝ)
    (hπ : IsInnerPolicy M D xhat x1hat) :
    vpi M xhat x1hat ≤ y M D := by
  have hall : ∀ k t, t + k = M.T → 2 ≤ t → ∀ x,
      riskE (M.ρ t) (fun ω => vhat M xhat t x ω) ≤ Qhat M D t x := by
    intro k
    induction k with
    | zero =>
      intro t htk ht2 x
      exact RRAux_CoherentSDDP_Inner_proposition_5.claim M hρ D hD xhat x1hat hπ t ht2
        (by omega) (fun h => absurd h (by omega)) x
    | succ k ih =>
      intro t htk ht2 x
      exact RRAux_CoherentSDDP_Inner_proposition_5.claim M hρ D hD xhat x1hat hπ t ht2
        (by omega) (fun _ => ih (t + 1) (by omega) (by omega)) x
  unfold vpi
  rw [← hπ.2.2]
  exact add_le_add_right (hall (M.T - 2) 2 (by omega) le_rfl x1hat) _

#print axioms solution
