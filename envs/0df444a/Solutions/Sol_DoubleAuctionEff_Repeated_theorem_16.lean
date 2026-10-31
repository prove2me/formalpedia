-- Prove2me | solution 1 for DoubleAuctionEff.Repeated.theorem_16
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T20:58:45.122984+00:00
-- url     : https://prove2.me/submissions/75737d97-a053-45f6-a184-a8ee2d6e77a6

import Mathlib
import Definitions.Def_DoubleAuctionEff_Repeated_Model
import Theorems.Thm_DoubleAuctionEff_Repeated_CS_le_of_indivRational
import Theorems.Thm_DoubleAuctionEff_Repeated_remark_6
import Theorems.Thm_DoubleAuctionEff_Repeated_auction_gain
import Theorems.Thm_DoubleAuctionEff_Repeated_C_bounded
import Theorems.Thm_DoubleAuctionEff_Repeated_theorem_11

open Matrix DoubleAuctionEff.Repeated Filter Topology

namespace DAEThm16Aux

theorem u_ne_top {J : Type*} {u : (J → ℝ) → EReal} {g : J → ℝ} (h1 : Assumption1 u g)
    (x : J → ℝ) : u x ≠ ⊤ := by
  intro h
  have hx : x ∈ dom u := by simp [dom, h]
  have := h1.2.2 x hx 1 one_pos
  rw [h] at this
  exact not_top_lt this

theorem le_indiff {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {r : ℝ}
    (h : u x0 ≤ u (x0 + y - r • g)) : (r : EReal) ≤ indiffPrice u g x0 y := by
  unfold indiffPrice
  exact le_iSup₂ (f := fun (r : ℝ) (_ : u x0 ≤ u (x0 + y - r • g)) => (r : EReal)) r h

theorem mem_dom_of_finite {J : Type*} {u : (J → ℝ) → EReal} {g x0 y : J → ℝ} {c : ℝ}
    (hc : indiffPrice u g x0 y = (c : EReal)) : x0 ∈ dom u := by
  by_contra hx
  simp only [dom, Set.mem_setOf_eq, not_lt, le_bot_iff] at hx
  have := le_indiff (u := u) (g := g) (x0 := x0) (y := y) (r := c + 1) (by simp [hx])
  rw [hc, EReal.coe_le_coe_iff] at this
  linarith

theorem CS_nonneg {I J : Type*} [Fintype I] (u : I → (J → ℝ) → EReal) (g : J → ℝ)
    (x : I → J → ℝ) : 0 ≤ CS u g x := by
  unfold CS
  refine le_trans ?_ (le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
    ∑ i, indiffPrice (u i) g (x i) (y i)) 0 (by simp))
  refine Finset.sum_nonneg fun i _ => ?_
  have := le_indiff (u := u i) (g := g) (x0 := x i) (y := 0) (r := 0) (by simp)
  simpa using this

theorem coe_sum {I : Type*} (s : Finset I) (f : I → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, EReal.coe_add, ih]

end DAEThm16Aux

open DAEThm16Aux in
theorem solution {I J : Type*} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J]
    [DecidableEq J] (u : I → (J → ℝ) → EReal) (g : J → ℝ) (x0 : I → J → ℝ)
    (h1 : ∀ i, Assumption1 (u i) g) (h3 : Assumption3 u) (h5 : ∀ i, Assumption5 (u i) g)
    (x y : ℕ → I → J → ℝ) (p : ℕ → J → ℝ) (hseq : IsAuctionSeq u g x0 x y p) :
    Bornology.IsBounded (Set.range x) ∧ Antitone (fun t => CS u g (x t)) ∧
      Filter.Tendsto (fun t => CS u g (x t)) Filter.atTop (nhds 0) ∧
      (∃ R : ℝ, 0 < R ∧ ∀ δ : I → ℝ, (∀ i, 0 < δ i ∧ Assumption5At (u i) g R (δ i)) →
        ∀ t : ℕ, 1 ≤ t → CS u g (x t) ≤
          (((1 / (t : ℝ)) * ∑ i, ((u i (x t i)).toReal - (u i (x0 i)).toReal) / δ i : ℝ) :
            EReal)) ∧
      (∀ xbar : I → J → ℝ, MapClusterPt xbar Filter.atTop x →
        IsDAEquilibrium u g xbar ∧ IsIndivRational u x0 xbar) ∧
      ((∀ i, Assumption4 (u i) g) → ∀ xbar : I → J → ℝ, MapClusterPt xbar Filter.atTop x →
        IsParetoEfficient u x0 xbar) := by
  obtain ⟨hx0eq, hstep⟩ := hseq
  have hsum : ∀ t, ∑ i, y (t + 1) i = 0 := fun t => (hstep t).1
  have hsg : ∀ t i, IsSupergrad (indiffPrice (u i) g (x t i)) (y (t + 1) i) (p (t + 1)) :=
    fun t => (hstep t).2.1
  have hrec : ∀ t i, x (t + 1) i =
      x t i + y (t + 1) i - (p (t + 1) ⬝ᵥ y (t + 1) i) • g := fun t => (hstep t).2.2
  choose c hc using fun t i => (hsg t i).1
  have hdom : ∀ t i, x t i ∈ dom (u i) := fun t i => mem_dom_of_finite (hc t i)
  -- Remark 6 at every auction
  have hR6 := fun t i => remark_6 (u i) g (x t i) (y (t + 1) i) (p (t + 1)) (h1 i) (hsg t i)
    (c t i) (hc t i)
  have hmono : ∀ t i, u i (x t i) ≤ u i (x (t + 1) i) := by
    intro t i; rw [hrec t i]; exact (hR6 t i).2.2.2.1
  have hmono' : ∀ i, Monotone (fun t => u i (x t i)) := fun i =>
    monotone_nat_of_le_succ fun t => hmono t i
  have hIR : ∀ t i, u i (x0 i) ≤ u i (x t i) := by
    intro t i; rw [← hx0eq]; exact hmono' i (Nat.zero_le t)
  have hfeas : ∀ t, ∑ i, x t i = ∑ i, x0 i := by
    intro t
    induction t with
    | zero => rw [hx0eq]
    | succ t ih =>
      rw [← ih]
      simp only [hrec t, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul,
        ← dotProduct_sum, hsum t, dotProduct_zero, zero_smul, add_zero, sub_zero]
  -- boundedness
  have hbdd : Bornology.IsBounded (Set.range x) := by
    have hC := C_bounded u g x0 h1 h3 (fun i => hx0eq ▸ hdom 0 i)
    refine hC.subset ?_
    rintro _ ⟨t, rfl⟩
    exact ⟨hfeas t, hIR t⟩
  -- monotonicity of CS
  have hCSle : ∀ t, CS u g (x (t + 1)) ≤ CS u g (x t) := fun t =>
    CS_le_of_indivRational u g (x t) (x (t + 1)) ((hfeas (t + 1)).trans (hfeas t).symm)
      (hmono t)
  have hanti : Antitone (fun t => CS u g (x t)) := antitone_nat_of_succ_le hCSle
  -- CS at each iterate equals the total surplus
  set cs : ℕ → ℝ := fun t => ∑ i, c t i with hcsdef
  have hCS : ∀ t, CS u g (x t) = ((cs t : ℝ) : EReal) := by
    intro t
    apply le_antisymm
    · unfold CS
      refine iSup₂_le fun y' hy' => ?_
      have hle : ∑ i, indiffPrice (u i) g (x t i) (y' i) ≤
          ∑ i, (((c t i + p (t + 1) ⬝ᵥ (y' i - y (t + 1) i)) : ℝ) : EReal) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := (hsg t i).2 (y' i)
        rwa [hc t i, ← EReal.coe_add] at this
      refine hle.trans (le_of_eq ?_)
      rw [← coe_sum, Finset.sum_add_distrib, ← dotProduct_sum, Finset.sum_sub_distrib, hy',
        hsum t, sub_zero, dotProduct_zero, add_zero]
    · unfold CS
      refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (y : I → J → ℝ) (_ : ∑ i, y i = 0) =>
        ∑ i, indiffPrice (u i) g (x t i) (y i)) (y (t + 1)) (hsum t))
      rw [coe_sum]; exact Finset.sum_congr rfl fun i _ => (hc t i).symm
  have hcsanti : Antitone cs := by
    intro a b hab
    have := hanti hab
    simp only [hCS] at this
    exact_mod_cast this
  set s : ℕ → I → ℝ := fun t i => c t i - p (t + 1) ⬝ᵥ y (t + 1) i with hsdef
  have hs0 : ∀ t i, 0 ≤ s t i := fun t i => (hR6 t i).1
  have hssum : ∀ t, ∑ i, s t i = cs t := by
    intro t
    simp only [s, cs, Finset.sum_sub_distrib, ← dotProduct_sum, hsum t, dotProduct_zero, sub_zero]
  have hscs : ∀ t i, s t i ≤ cs t := by
    intro t i
    rw [← hssum t]
    exact Finset.single_le_sum (fun j _ => hs0 t j) (Finset.mem_univ i)
  have hcs0 : ∀ t, 0 ≤ cs t := fun t => (hs0 t (Classical.arbitrary I)).trans (hscs t _)
  -- the radius R
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 hbdd
  have hB' : ∀ t i, ‖x t i‖ ≤ B := fun t i =>
    (norm_le_pi_norm (x t) i).trans (hB _ ⟨t, rfl⟩)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0 (Classical.arbitrary I))
  set R : ℝ := B + cs 0 * ‖g‖ + cs 0 + 1 with hRdef
  have hRpos : 0 < R := by have := hcs0 0; positivity
  -- real utilities
  set v : ℕ → I → ℝ := fun t i => (u i (x t i)).toReal with hvdef
  have hv : ∀ t i, u i (x t i) = ((v t i : ℝ) : EReal) := fun t i =>
    (EReal.coe_toReal (u_ne_top (h1 i) _) (ne_of_gt (hdom t i))).symm
  -- the gain inequality and the rate
  have hrate : ∀ δ : I → ℝ, (∀ i, 0 < δ i ∧ Assumption5At (u i) g R (δ i)) →
      ∀ t : ℕ, (t : ℝ) * cs t ≤ ∑ i, (v t i - v 0 i) / δ i := by
    intro δ hδ
    have hgain : ∀ t i, v t i + δ i * s t i ≤ v (t + 1) i := by
      intro t i
      have hball : x t i + y (t + 1) i - c t i • g ∈ Metric.closedBall (0 : J → ℝ) R := by
        rw [mem_closedBall_zero_iff]
        have he : x t i + y (t + 1) i - c t i • g = x (t + 1) i - s t i • g := by
          rw [hrec t i]; simp only [s, sub_smul]; abel
        rw [he]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hs0 t i)]
        have h1' := hB' (t + 1) i
        have h2' : s t i * ‖g‖ ≤ cs 0 * ‖g‖ :=
          mul_le_mul_of_nonneg_right ((hscs t i).trans (hcsanti (Nat.zero_le t))) (norm_nonneg _)
        have := hcs0 0
        linarith
      have hsur : s t i ≤ R := by
        have := (hscs t i).trans (hcsanti (Nat.zero_le t))
        have := hcs0 0
        have : 0 ≤ cs 0 * ‖g‖ := by positivity
        linarith
      have := auction_gain (u i) g (x t i) (y (t + 1) i) (p (t + 1)) (h1 i) (hsg t i) (c t i)
        (hc t i) R (δ i) hRpos (hδ i).2 hball hsur
      rw [← hrec t i, hv, hv, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
      exact this
    have hstep' : ∀ t, cs t ≤ ∑ i, (v (t + 1) i - v t i) / δ i := by
      intro t
      rw [← hssum t]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [le_div_iff₀ (hδ i).1]
      have := hgain t i
      linarith
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have h2 := hstep' t
      have h3' : ∑ i, (v (t + 1) i - v 0 i) / δ i =
          ∑ i, (v t i - v 0 i) / δ i + ∑ i, (v (t + 1) i - v t i) / δ i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
        ring
      rw [h3']
      have h4 : cs (t + 1) ≤ cs t := hcsanti (Nat.le_succ t)
      push_cast
      nlinarith [hcs0 (t + 1), (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
  -- upper bound of utilities along the sequence at a cluster point
  have hub : ∀ xbar : I → J → ℝ, MapClusterPt xbar atTop x → ∀ t i, u i (x t i) ≤ u i (xbar i) := by
    intro xbar hcl t i
    by_contra hlt
    push_neg at hlt
    have hev : ∀ᶠ w in 𝓝 xbar, u i (w i) < u i (x t i) :=
      ((continuous_apply i).tendsto xbar).eventually ((h1 i).1 _ _ hlt)
    have hfr := hcl.frequently hev
    obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually (eventually_ge_atTop t)).exists
    exact absurd (hmono' i hn2) (not_le.2 hn1)
  have hsumbar : ∀ xbar : I → J → ℝ, MapClusterPt xbar atTop x → ∑ i, xbar i = ∑ i, x0 i := by
    intro xbar hcl
    have hcl' : IsClosed {w : I → J → ℝ | ∑ i, w i = ∑ i, x0 i} :=
      isClosed_eq (by fun_prop) continuous_const
    exact hcl'.mem_of_mapClusterPt hcl (Eventually.of_forall hfeas)
  -- existence of a cluster point
  obtain ⟨xb, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd (fun n => ⟨n, rfl⟩)
  have hxbcl : MapClusterPt xb atTop x := MapClusterPt.of_comp hφ.tendsto_atTop hlim.mapClusterPt
  -- convergence
  have hlim0 : Tendsto (fun t => CS u g (x t)) atTop (𝓝 0) := by
    choose δ hδ using fun i => h5 i R hRpos
    have hδ' : ∀ i, 0 < δ i ∧ Assumption5At (u i) g R (δ i) := hδ
    set M : I → ℝ := fun i => (u i (xb i)).toReal
    have hM : ∀ i, u i (xb i) = ((M i : ℝ) : EReal) := fun i =>
      (EReal.coe_toReal (u_ne_top (h1 i) _)
        (ne_of_gt (lt_of_lt_of_le (hdom 0 i) (hub xb hxbcl 0 i)))).symm
    set K : ℝ := ∑ i, (M i - v 0 i) / δ i
    have hK : ∀ t : ℕ, (t : ℝ) * cs t ≤ K := by
      intro t
      refine (hrate δ hδ' t).trans (Finset.sum_le_sum fun i _ => ?_)
      have : v t i ≤ M i := by
        have := hub xb hxbcl t i
        rw [hv, hM] at this; exact_mod_cast this
      exact div_le_div_of_nonneg_right (by linarith) (hδ i).1.le
    have hreal : Tendsto cs atTop (𝓝 0) := by
      have hup : Tendsto (fun t : ℕ => K * (1 / (t : ℝ))) atTop (𝓝 (K * 0)) :=
        tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat
      rw [mul_zero] at hup
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
        (Eventually.of_forall hcs0) ?_
      filter_upwards [eventually_ge_atTop 1] with t ht
      have htpos : (0 : ℝ) < t := by exact_mod_cast ht
      rw [mul_one_div, le_div_iff₀ htpos, mul_comm]
      exact hK t
    have := EReal.tendsto_coe.2 hreal
    simpa [hCS] using this
  refine ⟨hbdd, hanti, hlim0, ⟨R, hRpos, fun δ hδ t ht => ?_⟩, ?_, ?_⟩
  · rw [hCS, EReal.coe_le_coe_iff]
    have htpos : (0 : ℝ) < t := by exact_mod_cast ht
    have : (t : ℝ) * cs t ≤ ∑ i, ((u i (x t i)).toReal - (u i (x0 i)).toReal) / δ i := by
      have := hrate δ hδ t; rw [← hx0eq]; exact this
    rw [one_div_mul_eq_div, le_div_iff₀ htpos, mul_comm]
    exact this
  · intro xbar hcl
    have hIRbar : IsIndivRational u x0 xbar := by
      intro i; rw [← hx0eq]; exact hub xbar hcl 0 i
    refine ⟨?_, hIRbar⟩
    unfold IsDAEquilibrium
    refine le_antisymm ?_ (CS_nonneg u g xbar)
    refine ge_of_tendsto' hlim0 fun t => ?_
    exact CS_le_of_indivRational u g (x t) xbar ((hsumbar xbar hcl).trans (hfeas t).symm)
      (hub xbar hcl t)
  · intro h4 xbar hcl
    have heq : IsDAEquilibrium u g xbar := by
      unfold IsDAEquilibrium
      refine le_antisymm ?_ (CS_nonneg u g xbar)
      refine ge_of_tendsto' hlim0 fun t => ?_
      exact CS_le_of_indivRational u g (x t) xbar ((hsumbar xbar hcl).trans (hfeas t).symm)
        (hub xbar hcl t)
    have hP := (theorem_11 u g h1).2 h4 xbar heq
    refine ⟨hsumbar xbar hcl, ?_⟩
    rintro ⟨x', hf', hge, hlt⟩
    exact hP.2 ⟨x', hf'.trans (hsumbar xbar hcl).symm, hge, hlt⟩
