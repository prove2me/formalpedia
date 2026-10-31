-- Prove2me | solution 1 for FMLPricing.BranchBound.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T15:57:40.86681+00:00
-- url     : https://prove2.me/submissions/97c186db-9221-412e-9d19-7519115ff9a4

import Mathlib
import Definitions.Def_FMLPricing_BranchBound_Model
import Theorems.Thm_FMLPricing_BranchBound_proposition_1
import Theorems.Thm_FMLPricing_BranchBound_lemma_1
import Theorems.Thm_FMLPricing_BranchBound_equation_5
import Theorems.Thm_FMLPricing_BranchBound_proposition_2
import Theorems.Thm_FMLPricing_BranchBound_proposition_7
import Theorems.Thm_FMLPricing_BranchBound_corollary_1

open FMLPricing.BranchBound

namespace FMLBBSol

variable {m n : ℕ} (I : FML m n)

lemma denom_pos (c : Fin m) (p : Fin n → ℝ) : 0 < denom I c p := by
  unfold denom; positivity

lemma q0_pos (p : Fin n → ℝ) (c : Fin m) : 0 < q0 I p c := by
  unfold q0; exact one_div_pos.mpr (denom_pos I c p)

lemma q_pos (c : Fin m) (i : Fin n) (p : Fin n → ℝ) : 0 < q I c i p := by
  unfold q; exact div_pos (Real.exp_pos _) (denom_pos I c p)

lemma q0_mono (hI : Standing I) {p p' : Fin n → ℝ} (h : p ≤ p') (c : Fin m) :
    q0 I p c ≤ q0 I p' c := by
  unfold q0
  apply one_div_le_one_div_of_le (denom_pos I c p')
  unfold denom
  refine (add_le_add_iff_left 1).mpr (Finset.sum_le_sum fun j _ => ?_)
  exact Real.exp_le_exp.mpr (by nlinarith [hI.b_pos j, h j])

lemma q0_strictMono (hI : Standing I) {p p' : Fin n → ℝ} (h : ∀ j, p j < p' j) (c : Fin m) :
    q0 I p c < q0 I p' c := by
  unfold q0
  apply one_div_lt_one_div_of_lt (denom_pos I c p')
  unfold denom
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
  refine (add_lt_add_iff_left 1).mpr (Finset.sum_lt_sum_of_nonempty hne fun j _ => ?_)
  exact Real.exp_lt_exp.mpr (by nlinarith [hI.b_pos j, h j])

lemma term_le (hI : Standing I) (c : Fin m) (i : Fin n) (p : Fin n → ℝ) :
    p i * q I c i p ≤ Real.exp (I.a c i - 1) / I.b i := by
  have hb := hI.b_pos i
  have hq := q_pos I c i p
  rcases le_or_gt (p i) 0 with hp | hp
  · have : p i * q I c i p ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hq.le
    exact this.trans (div_pos (Real.exp_pos _) hb).le
  · have hqle : q I c i p ≤ Real.exp (I.a c i - I.b i * p i) := by
      unfold q
      apply div_le_self (Real.exp_pos _).le
      unfold denom
      have : 0 ≤ ∑ j, Real.exp (I.a c j - I.b j * p j) :=
        Finset.sum_nonneg fun j _ => (Real.exp_pos _).le
      linarith
    have h1 : p i * q I c i p ≤ p i * Real.exp (I.a c i - I.b i * p i) :=
      mul_le_mul_of_nonneg_left hqle hp.le
    have h2 : I.b i * p i ≤ Real.exp (I.b i * p i - 1) := by
      have := Real.add_one_le_exp (I.b i * p i - 1); linarith
    have h3 : Real.exp (I.a c i - I.b i * p i) * Real.exp (I.b i * p i - 1)
        = Real.exp (I.a c i - 1) := by rw [← Real.exp_add]; ring_nf
    rw [le_div_iff₀ hb]
    have he := Real.exp_pos (I.a c i - I.b i * p i)
    calc p i * q I c i p * I.b i ≤ p i * Real.exp (I.a c i - I.b i * p i) * I.b i :=
          mul_le_mul_of_nonneg_right h1 hb.le
      _ = Real.exp (I.a c i - I.b i * p i) * (I.b i * p i) := by ring
      _ ≤ Real.exp (I.a c i - I.b i * p i) * Real.exp (I.b i * p i - 1) :=
          mul_le_mul_of_nonneg_left h2 he.le
      _ = Real.exp (I.a c i - 1) := h3

lemma segRev_bdd (hI : Standing I) (c : Fin m) :
    BddAbove (Set.range fun p : Fin n → ℝ => ∑ i, p i * q I c i p) := by
  refine ⟨∑ i, Real.exp (I.a c i - 1) / I.b i, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact Finset.sum_le_sum fun i _ => term_le I hI c i p

lemma segRev_pLo_pos (hI : Standing I) (c : Fin m) :
    0 < ∑ i, pLo I i * q I c i (pLo I) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hI.n_pos⟩, Finset.mem_univ _⟩
  exact Finset.sum_pos (fun i _ => mul_pos (inv_pos.mpr (hI.b_pos i)) (q_pos I c i _)) hne

lemma segMax_pos (hI : Standing I) (c : Fin m) : 0 < segMax I c :=
  (segRev_pLo_pos I hI c).trans_le (le_csSup (segRev_bdd I hI c) ⟨pLo I, rfl⟩)

lemma pLo_lt_pHi (hI : Standing I) (j : Fin n) : pLo I j < pHi I j := by
  have hc : 0 < segMax I ⟨0, hI.m_pos⟩ := segMax_pos I hI _
  have : segMax I ⟨0, hI.m_pos⟩ ≤ ⨆ c : Fin m, segMax I c :=
    le_ciSup (Finite.bddAbove_range _) _
  simp only [pLo, pHi]; linarith

lemma pLo_mem (hI : Standing I) : pLo I ∈ priceBox I :=
  ⟨le_rfl, fun j => (pLo_lt_pHi I hI j).le⟩

lemma q0pLo_mem (hI : Standing I) : q0 I (pLo I) ∈ Xset I := ⟨pLo I, pLo_mem I hI, rfl⟩

lemma r0_spec (hI : Standing I) (c : Fin m) :
    q0 I (pHi I) c - q0 I (pLo I) c ≤ 2 * r0 I := by
  have : q0 I (pHi I) c - q0 I (pLo I) c ≤ ⨆ c : Fin m, (q0 I (pHi I) c - q0 I (pLo I) c) :=
    le_ciSup (f := fun c => q0 I (pHi I) c - q0 I (pLo I) c) (Finite.bddAbove_range _) c
  simp only [r0]; linarith

lemma r0_pos (hI : Standing I) : 0 < r0 I := by
  have h := q0_strictMono I hI (pLo_lt_pHi I hI) ⟨0, hI.m_pos⟩
  have := r0_spec I hI ⟨0, hI.m_pos⟩
  linarith

lemma Pi_pLo_pos (hI : Standing I) : 0 < Pi I (pLo I) := by
  have hm : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, hI.m_pos⟩, Finset.mem_univ _⟩
  unfold Pi
  exact Finset.sum_pos (fun c _ => mul_pos (hI.w_pos c) (segRev_pLo_pos I hI c)) hm

lemma Xset_bounds (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) (c : Fin m) :
    q0 I (pLo I) c ≤ x c ∧ x c ≤ q0 I (pHi I) c := by
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨q0_mono I hI hp.1 c, q0_mono I hI hp.2 c⟩

lemma feas_eq (x : Fin m → ℝ) : cnstrFeasible I x =
    Set.Icc (zLo I) (zHi I) ∩ ⋂ c, {z | 1 + ∑ j, s I c j * z j = 1 / x c} := by
  ext z; simp [cnstrFeasible]

lemma feas_compact (x : Fin m → ℝ) : IsCompact (cnstrFeasible I x) := by
  rw [feas_eq]
  exact isCompact_Icc.inter_right (isClosed_iInter fun c => isClosed_eq (by fun_prop)
    continuous_const)

lemma obj_cont (x : Fin m → ℝ) : Continuous (cnstrObj I x) := by
  unfold cnstrObj
  fun_prop

lemma feas_nonempty (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) :
    (cnstrFeasible I x).Nonempty := by
  obtain ⟨hbij, -, -⟩ := lemma_1 I hI x hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact ⟨zOf I p, hbij.mapsTo ⟨hp, fun c => rfl⟩⟩

lemma exists_max (hI : Standing I) {x : Fin m → ℝ} (hx : x ∈ Xset I) :
    ∃ z, IsCnstrMax I x z := by
  obtain ⟨z, hz, hmax⟩ := (feas_compact I x).exists_isMaxOn (feas_nonempty I hI hx)
    (obj_cont I x).continuousOn
  exact ⟨z, hz, fun z' hz' => hmax hz'⟩

lemma le_piX {x : Fin m → ℝ} {z : Fin n → ℝ} (hz : z ∈ cnstrFeasible I x) :
    cnstrObj I x z ≤ piX I x :=
  le_csSup ((feas_compact I x).bddAbove_image (obj_cont I x).continuousOn)
    (Set.mem_image_of_mem _ hz)

lemma Pi_pLo_le (hI : Standing I) : Pi I (pLo I) ≤ piX I (q0 I (pLo I)) := by
  obtain ⟨hbij, hobj, -⟩ := lemma_1 I hI _ (q0pLo_mem I hI)
  rw [hobj (pLo I) (pLo_mem I hI) (fun c => rfl)]
  exact le_piX I (hbij.mapsTo ⟨pLo_mem I hI, fun c => rfl⟩)

lemma mem_Rbox_of_cov (hI : Standing I) {x y : Fin m → ℝ} {r : ℝ} (hy : y ∈ Xset I)
    (h : ∀ c, |y c - x c| ≤ r) : y ∈ Rbox I x r ∩ Xset I := by
  refine ⟨⟨fun c => ?_, fun c => ?_⟩, hy⟩
  · have h1 := Xset_bounds I hI hy c
    have h2 := abs_le.mp (h c)
    show max (x c - r) (q0 I (pLo I) c) ≤ y c
    exact max_le (by linarith) h1.1
  · have h1 := Xset_bounds I hI hy c
    have h2 := abs_le.mp (h c)
    show y c ≤ min (x c + r) (q0 I (pHi I) c)
    exact le_min (by linarith) h1.2

lemma noexit {hi : EReal} {L t a : ℝ} (ha : 0 < a) (hhi : hi ≤ ((L + t : ℝ) : EReal))
    (h : a * (L + t) ≤ L) : ¬ ((a : EReal) * hi > (L : EReal)) := by
  induction hi using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos ha]; exact not_lt_bot
  | coe h' =>
    rw [← EReal.coe_mul, gt_iff_lt, EReal.coe_lt_coe_iff, not_lt]
    have := EReal.coe_le_coe_iff.mp hhi
    nlinarith
  | top => exact absurd hhi (not_le.mpr (EReal.coe_lt_top _))

lemma exit_bound {hi : EReal} {L π a : ℝ} (ha : 0 < a) (hπ : (π : EReal) ≤ hi)
    (h : ¬ ((a : EReal) * hi > (L : EReal))) : a * π ≤ L := by
  induction hi using EReal.rec with
  | bot => exact absurd (le_bot_iff.mp hπ) (EReal.coe_ne_bot _)
  | coe h' =>
    rw [← EReal.coe_mul, gt_iff_lt, EReal.coe_lt_coe_iff, not_lt] at h
    have := EReal.coe_le_coe_iff.mp hπ
    nlinarith
  | top => rw [EReal.coe_mul_top_of_pos ha] at h; exact absurd (EReal.coe_lt_top _) h

def InvAcc (K r lo0 : ℝ) (X1 : Finset (Fin m → ℝ)) (A : LoopAcc m) : Prop :=
  A.xs ∈ Xset I ∧ A.lo ≤ piX I A.xs ∧ lo0 ≤ A.lo ∧
    A.hi ≤ ((A.lo + 2 * r * K : ℝ) : EReal) ∧ A.X2 ⊆ X1

def PAcc (r : ℝ) (xst : Fin m → ℝ) (A : LoopAcc m) : Prop :=
  ((piX I xst : ℝ) : EReal) ≤ A.hi ∧
    (piX I xst ≤ A.lo ∨ ∃ x ∈ A.X2, ∀ c, |xst c - x c| ≤ r)

def InvS (xst : Fin m → ℝ) (S : BNBState m) : Prop :=
  0 < S.r ∧ (∀ x ∈ S.X1, ∀ c, q0 I (pLo I) c + S.r ≤ x c) ∧ S.xs ∈ Xset I ∧
    S.lo ≤ piX I S.xs ∧ Pi I (pLo I) ≤ S.lo ∧
    (piX I xst ≤ S.lo ∨ ∃ x ∈ S.X1, ∀ c, |xst c - x c| ≤ S.r)

section Run

variable (hI : Standing I) (U : (Fin m → ℝ) → ℝ → ℝ) (K₀ : ℝ)
  (hU1 : ∀ x ∈ Xset I, ∀ r > 0, ∀ x' ∈ Rbox I x r ∩ Xset I, piX I x' ≤ U x r)
  (hU2 : ∀ x ∈ Xset I, ∀ r > 0, U x r ≤ piX I x + r * K₀)
  (sol : (Fin m → ℝ) → ℝ → LPVars m n)
  (hsol : ∀ x r, (∀ c, 0 < x c) → 0 < r → LPFeasible I x r → IsLPSolution I x r (sol x r))
  (xst : Fin m → ℝ) (hxst : xst ∈ Xset I)

include hI hU1 hU2 hsol hxst

lemma visit_spec {r lo0 : ℝ} (hr : 0 < r) {X1 : Finset (Fin m → ℝ)}
    (hX1 : ∀ x ∈ X1, ∀ c, q0 I (pLo I) c + r ≤ x c)
    {x : Fin m → ℝ} (hx : x ∈ X1) {A : LoopAcc m} (hA : InvAcc I (max K₀ 0) r lo0 X1 A) :
    InvAcc I (max K₀ 0) r lo0 X1 (bnbVisit I U sol r A x) ∧
    (PAcc I r xst A → PAcc I r xst (bnbVisit I U sol r A x)) ∧
    ((∀ c, |xst c - x c| ≤ r) → PAcc I r xst (bnbVisit I U sol r A x)) := by
  obtain ⟨hAxs, hAlo, hAlo0, hAhi, hAX2⟩ := hA
  have hxpos : ∀ c, 0 < x c := fun c => by linarith [q0_pos I (pLo I) c, hX1 x hx c]
  by_cases hne : (Rbox I x r ∩ Xset I).Nonempty
  swap
  · have hv : bnbVisit I U sol r A x = A := by simp only [bnbVisit, if_neg hne]
    rw [hv]
    exact ⟨⟨hAxs, hAlo, hAlo0, hAhi, hAX2⟩, id,
      fun hc => absurd ⟨xst, mem_Rbox_of_cov I hI hxst hc⟩ hne⟩
  have hLP := (proposition_7 I hI x hxpos r hr).mp hne
  have hs := hsol x r hxpos hr hLP
  obtain ⟨⟨hδR, hδX⟩, -⟩ := corollary_1 I hI x hxpos r hr hne (sol x r) hs
  set xδ := chi x (sol x r).δp (sol x r).δm with hxδ
  set rδ := r + ‖x - xδ‖ with hrδ
  have hnorm : ‖x - xδ‖ ≤ r := by
    rw [pi_norm_le_iff_of_nonneg hr.le]
    intro c
    have h1 := hδR.1 c
    have h2 := hδR.2 c
    simp only [xLo, xHi] at h1 h2
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;>
      linarith [le_max_left (x c - r) (q0 I (pLo I) c), min_le_left (x c + r) (q0 I (pHi I) c)]
  have hrδpos : 0 < rδ := by have := norm_nonneg (x - xδ); linarith
  have hK0 : K₀ ≤ max K₀ 0 := le_max_left _ _
  have hK1 : 0 ≤ max K₀ 0 := le_max_right _ _
  have hUb : U xδ rδ ≤ piX I xδ + 2 * r * max K₀ 0 := by
    have h1 := hU2 xδ hδX rδ hrδpos
    have h2 : rδ * K₀ ≤ rδ * max K₀ 0 := mul_le_mul_of_nonneg_left hK0 hrδpos.le
    have h3 : rδ * max K₀ 0 ≤ 2 * r * max K₀ 0 := by
      apply mul_le_mul_of_nonneg_right _ hK1; linarith
    linarith
  have hv : bnbVisit I U sol r A x =
      ⟨if piX I xδ ≥ A.lo then piX I xδ else A.lo,
       if ((U xδ rδ : ℝ) : EReal) ≥ A.hi then ((U xδ rδ : ℝ) : EReal) else A.hi,
       if U xδ rδ ≥ (if piX I xδ ≥ A.lo then piX I xδ else A.lo) then insert x A.X2 else A.X2,
       if piX I xδ ≥ A.lo then xδ else A.xs⟩ := by
    unfold bnbVisit; rw [if_pos hne]
  rw [hv]
  have key : ∀ (lo₁ : ℝ) (hi₁ : EReal) (X2₁ : Finset (Fin m → ℝ)) (xs₁ : Fin m → ℝ),
      ((lo₁ = piX I xδ ∧ xs₁ = xδ) ∨ (lo₁ = A.lo ∧ xs₁ = A.xs)) →
      A.lo ≤ lo₁ → piX I xδ ≤ lo₁ →
      (hi₁ = ((U xδ rδ : ℝ) : EReal) ∨ hi₁ = A.hi) → A.hi ≤ hi₁ →
      ((U xδ rδ : ℝ) : EReal) ≤ hi₁ →
      A.X2 ⊆ X2₁ → X2₁ ⊆ insert x A.X2 → (lo₁ ≤ U xδ rδ → x ∈ X2₁) →
      InvAcc I (max K₀ 0) r lo0 X1 ⟨lo₁, hi₁, X2₁, xs₁⟩ ∧
      (PAcc I r xst A → PAcc I r xst ⟨lo₁, hi₁, X2₁, xs₁⟩) ∧
      ((∀ c, |xst c - x c| ≤ r) → PAcc I r xst ⟨lo₁, hi₁, X2₁, xs₁⟩) := by
    intro lo₁ hi₁ X2₁ xs₁ F1 F2 F3 F4 F5 F6 F7 F8 F9
    refine ⟨⟨?_, ?_, hAlo0.trans F2, ?_, F8.trans (Finset.insert_subset hx hAX2)⟩, ?_, ?_⟩
    · rcases F1 with ⟨-, h⟩ | ⟨-, h⟩ <;> simp only [h] <;> assumption
    · rcases F1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp only [h1, h2]
      · exact le_rfl
      · exact hAlo
    · show hi₁ ≤ ((lo₁ + 2 * r * max K₀ 0 : ℝ) : EReal)
      rcases F4 with h | h <;> rw [h]
      · exact EReal.coe_le_coe_iff.mpr (by linarith)
      · exact hAhi.trans (EReal.coe_le_coe_iff.mpr (by linarith))
    · rintro ⟨h1, h2⟩
      exact ⟨h1.trans F5, h2.imp (fun h => h.trans F2) (fun ⟨y, hy, hc⟩ => ⟨y, F7 hy, hc⟩)⟩
    · intro hc
      have hcov : ∀ c, |xst c - xδ c| ≤ rδ := by
        intro c
        have h1 := abs_sub_le (xst c) (x c) (xδ c)
        have h2 : |x c - xδ c| ≤ ‖x - xδ‖ := by
          have := norm_le_pi_norm (x - xδ) c
          rwa [Pi.sub_apply, Real.norm_eq_abs] at this
        linarith [hc c]
      have hle := hU1 xδ hδX rδ hrδpos xst (mem_Rbox_of_cov I hI hxst hcov)
      refine ⟨(EReal.coe_le_coe_iff.mpr hle).trans F6, ?_⟩
      by_cases hlt : lo₁ ≤ U xδ rδ
      · exact Or.inr ⟨x, F9 hlt, hc⟩
      · exact Or.inl (by show piX I xst ≤ lo₁; linarith)
  apply key
  · split_ifs <;> simp
  · split_ifs <;> linarith
  · split_ifs <;> linarith
  · split_ifs <;> simp
  · split_ifs with h
    · exact h
    · exact le_rfl
  · split_ifs with h
    · exact le_rfl
    · exact (not_le.mp h).le
  · split_ifs <;> first | exact Finset.subset_insert _ _ | exact Finset.Subset.refl _
  · split_ifs <;> first | exact Finset.subset_insert _ _ | exact Finset.Subset.refl _
  · intro h
    rw [if_pos h]
    exact Finset.mem_insert_self _ _

lemma fold_spec {r lo0 : ℝ} (hr : 0 < r) {X1 : Finset (Fin m → ℝ)}
    (hX1 : ∀ x ∈ X1, ∀ c, q0 I (pLo I) c + r ≤ x c) (l : List (Fin m → ℝ))
    (hl : ∀ x ∈ l, x ∈ X1) : ∀ A : LoopAcc m, InvAcc I (max K₀ 0) r lo0 X1 A →
      InvAcc I (max K₀ 0) r lo0 X1 (l.foldl (bnbVisit I U sol r) A) ∧
      (PAcc I r xst A ∨ (∃ x ∈ l, ∀ c, |xst c - x c| ≤ r) →
        PAcc I r xst (l.foldl (bnbVisit I U sol r) A)) := by
  induction l with
  | nil =>
    intro A hA
    refine ⟨hA, fun h => h.elim id ?_⟩
    rintro ⟨x, hx, -⟩
    exact absurd hx List.not_mem_nil
  | cons y l ih =>
    intro A hA
    rw [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := visit_spec I hI U K₀ hU1 hU2 sol hsol xst hxst hr hX1
      (hl y List.mem_cons_self) hA
    obtain ⟨ih1, ih2⟩ := ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _ h1
    refine ⟨ih1, fun h => ih2 ?_⟩
    rcases h with h | ⟨x, hx, hc⟩
    · exact Or.inl (h2 h)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl (h3 hc)
      · exact Or.inr ⟨x, hx, hc⟩

lemma body_spec (enum : Finset (Fin m → ℝ) → List (Fin m → ℝ))
    (henum : ∀ S, (enum S).Nodup ∧ (enum S).toFinset = S) (S : BNBState m)
    (hS : InvS I xst S) :
    InvS I xst (bnbBody I U sol enum S) ∧ (bnbBody I U sol enum S).r = S.r / 2 ∧
      (bnbBody I U sol enum S).hi ≤
        (((bnbBody I U sol enum S).lo + 2 * S.r * max K₀ 0 : ℝ) : EReal) ∧
      (piX I xst ≤ (bnbBody I U sol enum S).lo ∨
        ((piX I xst : ℝ) : EReal) ≤ (bnbBody I U sol enum S).hi) := by
  obtain ⟨hr, hpos, hxs, hlo, hPlo, hcov⟩ := hS
  set A := (enum S.X1).foldl (bnbVisit I U sol S.r) ⟨S.lo, ⊥, ∅, S.xs⟩ with hAdef
  have hb : bnbBody I U sol enum S =
      ⟨A.lo, A.hi, S.r / 2, A.X2.biUnion (children (S.r / 2)), A.xs⟩ := rfl
  have hl : ∀ x ∈ enum S.X1, x ∈ S.X1 := fun x hx => by
    rw [← (henum S.X1).2]; exact List.mem_toFinset.mpr hx
  have hA0 : InvAcc I (max K₀ 0) S.r S.lo S.X1 ⟨S.lo, ⊥, ∅, S.xs⟩ :=
    ⟨hxs, hlo, le_rfl, bot_le, Finset.empty_subset _⟩
  obtain ⟨hAinv, hAP⟩ := fold_spec I hI U K₀ hU1 hU2 sol hsol xst hxst hr hpos
    (enum S.X1) hl _ hA0
  obtain ⟨hAxs, hAlo, hAlo0, hAhi, hAX2⟩ := hAinv
  have hP : piX I xst ≤ A.lo ∨ PAcc I S.r xst A := by
    rcases hcov with h | ⟨x, hx, hc⟩
    · exact Or.inl (h.trans hAlo0)
    · refine Or.inr (hAP (Or.inr ⟨x, ?_, hc⟩))
      apply List.mem_toFinset.mp
      rw [(henum S.X1).2]; exact hx
  rw [hb]
  refine ⟨⟨by show 0 < S.r / 2; linarith, ?_, hAxs, hAlo, hPlo.trans hAlo0, ?_⟩, rfl, hAhi, ?_⟩
  · intro y hy c
    obtain ⟨x, hx, hy⟩ := Finset.mem_biUnion.mp hy
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp hy
    have := hpos x (hAX2 hx) c
    show q0 I (pLo I) c + S.r / 2 ≤ _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> linarith
  · rcases hP with h | ⟨-, h | ⟨x, hx, hc⟩⟩
    · exact Or.inl h
    · exact Or.inl h
    · refine Or.inr ⟨x + (S.r / 2) • fun c => if decide (x c ≤ xst c) then (1 : ℝ) else -1,
        Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr
          ⟨fun c => decide (x c ≤ xst c), Finset.mem_univ _, rfl⟩⟩, fun c => ?_⟩
      have := abs_le.mp (hc c)
      show |xst c - (x c + S.r / 2 * (if decide (x c ≤ xst c) then (1 : ℝ) else -1))| ≤ S.r / 2
      rw [abs_le]
      split_ifs with h
      · simp at h; constructor <;> linarith
      · simp at h; constructor <;> linarith
  · rcases hP with h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr h1

end Run

end FMLBBSol

namespace FMLBBSol

variable {m n : ℕ} (I : FML m n)

lemma run_succ (U : (Fin m → ℝ) → ℝ → ℝ) (sol : (Fin m → ℝ) → ℝ → LPVars m n)
    (enum : Finset (Fin m → ℝ) → List (Fin m → ℝ)) (k : ℕ) :
    bnbRun I U sol enum (k + 1) = bnbBody I U sol enum (bnbRun I U sol enum k) :=
  Function.iterate_succ_apply' _ _ _

lemma init_inv (hI : Standing I) (xst : Fin m → ℝ) (hxst : xst ∈ Xset I) :
    InvS I xst (bnbInit I) := by
  refine ⟨r0_pos I hI, ?_, q0pLo_mem I hI, Pi_pLo_le I hI, le_rfl, Or.inr ?_⟩
  · intro x hx c
    rw [show (bnbInit I).X1 = {q0 I (pLo I) + fun _ => r0 I} from rfl,
      Finset.mem_singleton] at hx
    subst hx
    show q0 I (pLo I) c + r0 I ≤ q0 I (pLo I) c + r0 I
    exact le_rfl
  · refine ⟨q0 I (pLo I) + fun _ => r0 I, Finset.mem_singleton_self _, fun c => ?_⟩
    have h1 := Xset_bounds I hI hxst c
    have h2 := r0_spec I hI c
    show |xst c - (q0 I (pLo I) c + r0 I)| ≤ r0 I
    rw [abs_le]; constructor <;> linarith

end FMLBBSol

open FMLBBSol in
theorem solution {m n : ℕ} (I : FML m n) (hI : Standing I) (ε : ℝ) (hε : 0 < ε)
    (U : (Fin m → ℝ) → ℝ → ℝ) (K₀ : ℝ)
    (hU1 : ∀ x ∈ Xset I, ∀ r > 0, ∀ x' ∈ Rbox I x r ∩ Xset I, piX I x' ≤ U x r)
    (hU2 : ∀ x ∈ Xset I, ∀ r > 0, U x r ≤ piX I x + r * K₀)
    (sol : (Fin m → ℝ) → ℝ → LPVars m n)
    (hsol : ∀ x r, (∀ c, 0 < x c) → 0 < r → LPFeasible I x r → IsLPSolution I x r (sol x r))
    (enum : Finset (Fin m → ℝ) → List (Fin m → ℝ))
    (henum : ∀ S, (enum S).Nodup ∧ (enum S).toFinset = S) :
    ∃ k : ℕ, ¬ bnbCond ε (bnbRun I U sol enum k) ∧
      (∀ j < k, bnbCond ε (bnbRun I U sol enum j)) ∧
      (bnbRun I U sol enum k).xs ∈ Xset I ∧
      (∃ z', IsCnstrMax I (bnbRun I U sol enum k).xs z') ∧
      (∃ pstar : Fin n → ℝ, ∀ p, Pi I p ≤ Pi I pstar) ∧
      ∀ z', IsCnstrMax I (bnbRun I U sol enum k).xs z' →
        ∀ pstar : Fin n → ℝ, (∀ p, Pi I p ≤ Pi I pstar) →
          (1 - ε) * Pi I pstar ≤ Pi I (priceOf I z') := by
  obtain ⟨x₀, hx₀, -, -, hG, -, -⟩ := equation_5 I hI
  have hmax : ∀ x ∈ Xset I, piX I x ≤ piX I x₀ := fun x hx => hG.2 ⟨x, hx, rfl⟩
  set K := max K₀ 0 with hK
  have hK1 : 0 ≤ K := le_max_right _ _
  set P := Pi I (pLo I) with hP
  have hPpos : 0 < P := Pi_pLo_pos I hI
  have hπP : P ≤ piX I x₀ := (Pi_pLo_le I hI).trans (hmax _ (q0pLo_mem I hI))
  have hrun : ∀ k, InvS I x₀ (bnbRun I U sol enum k) ∧
      (bnbRun I U sol enum k).r = r0 I / 2 ^ k := by
    intro k
    induction k with
    | zero => exact ⟨init_inv I hI x₀ hx₀, by simp [bnbRun, bnbInit]⟩
    | succ k ih =>
      obtain ⟨h1, h2, -, -⟩ := body_spec I hI U K₀ hU1 hU2 sol hsol x₀ hx₀ enum henum _ ih.1
      rw [run_succ]
      refine ⟨h1, ?_⟩
      rw [h2, ih.2, pow_succ]; ring
  have hstep : ∀ k, (bnbRun I U sol enum (k + 1)).hi ≤
        (((bnbRun I U sol enum (k + 1)).lo + 2 * (r0 I / 2 ^ k) * K : ℝ) : EReal) ∧
      (piX I x₀ ≤ (bnbRun I U sol enum (k + 1)).lo ∨
        ((piX I x₀ : ℝ) : EReal) ≤ (bnbRun I U sol enum (k + 1)).hi) := by
    intro k
    obtain ⟨-, -, h3, h4⟩ := body_spec I hI U K₀ hU1 hU2 sol hsol x₀ hx₀ enum henum _ (hrun k).1
    rw [run_succ, ← (hrun k).2]
    exact ⟨h3, h4⟩
  have hcond0 : ε < 1 → bnbCond ε (bnbRun I U sol enum 0) := by
    intro h
    show ((1 - ε : ℝ) : EReal) * ⊤ > ((Pi I (pLo I) : ℝ) : EReal)
    rw [EReal.coe_mul_top_of_pos (by linarith)]
    exact EReal.coe_lt_top _
  have hex : ∃ k, ¬ bnbCond ε (bnbRun I U sol enum k) := by
    by_cases hε1 : 1 ≤ ε
    · refine ⟨0, ?_⟩
      show ¬ (((1 - ε : ℝ) : EReal) * ⊤ > ((Pi I (pLo I) : ℝ) : EReal))
      rcases eq_or_lt_of_le hε1 with h | h
      · rw [← h, sub_self, EReal.coe_zero, zero_mul, gt_iff_lt, not_lt]
        exact EReal.coe_nonneg.mpr hPpos.le
      · rw [EReal.coe_mul_top_of_neg (by linarith)]
        exact not_lt_bot
    · push_neg at hε1
      obtain ⟨N, hN⟩ := exists_nat_gt (2 * r0 I * K / (ε * P))
      have hN2 : (N : ℝ) ≤ 2 ^ N := by exact_mod_cast (Nat.lt_two_pow_self).le
      have hεP : 0 < ε * P := mul_pos hε hPpos
      have ht : 2 * (r0 I / 2 ^ N) * K ≤ ε * P := by
        have h1 : 2 * r0 I * K < N * (ε * P) := (div_lt_iff₀ hεP).mp hN
        have h2 : 2 * r0 I * K ≤ 2 ^ N * (ε * P) :=
          h1.le.trans (mul_le_mul_of_nonneg_right hN2 hεP.le)
        have h2N : (0 : ℝ) < 2 ^ N := by positivity
        rw [show 2 * (r0 I / 2 ^ N) * K = 2 * r0 I * K / 2 ^ N by ring, div_le_iff₀ h2N]
        linarith
      refine ⟨N + 1, ?_⟩
      obtain ⟨h1, -⟩ := hstep N
      have hlo : P ≤ (bnbRun I U sol enum (N + 1)).lo := (hrun (N + 1)).1.2.2.2.2.1
      have htn : 0 ≤ 2 * (r0 I / 2 ^ N) * K := by
        have := r0_pos I hI; positivity
      refine noexit (by linarith) h1 ?_
      nlinarith [mul_nonneg hε.le htn, mul_le_mul_of_nonneg_left hlo hε.le]
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_not.mp (Nat.find_min hex hj),
    (hrun _).1.2.2.1, exists_max I hI (hrun _).1.2.2.1, (proposition_1 I hI).1, ?_⟩
  intro z' hz' pstar hpstar
  set k := Nat.find hex with hkdef
  obtain ⟨-, -, hxs, hloxs, hPlo, -⟩ := (hrun k).1
  have hfinal : (1 - ε) * piX I x₀ ≤ (bnbRun I U sol enum k).lo := by
    by_cases hε1 : 1 ≤ ε
    · nlinarith
    · push_neg at hε1
      have hk : k ≠ 0 := by
        intro h0
        have hs := Nat.find_spec hex
        rw [← hkdef, h0] at hs
        exact hs (hcond0 hε1)
      obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hex' := Nat.find_spec hex
      rw [← hkdef, hj] at hex'
      rw [hj]
      rcases (hstep j).2 with h | h
      · nlinarith
      · exact exit_bound (by linarith) h hex'
  have h2 := proposition_2 I hI _ hxs z' hz' ε hε (fun x₁ hx₁ hmax₁ => by
    have : piX I x₁ = piX I x₀ := le_antisymm (hmax _ hx₁) (hmax₁ _ hx₀)
    rw [this]; linarith)
  have hbox := (proposition_1 I hI).2 pstar hpstar
  exact h2.2 pstar ⟨fun j => (hbox j).1, fun j => (hbox j).2⟩ (fun p _ => hpstar p)
