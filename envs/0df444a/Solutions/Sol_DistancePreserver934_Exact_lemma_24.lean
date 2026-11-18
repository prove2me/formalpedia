-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_24
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:14:18.453714+00:00
-- url     : https://prove2.me/submissions/abdd849f-c0cc-4855-a7cf-1ffad8bc017a

import Theorems.Thm_DistancePreserver934_Exact_lemma_21
import Definitions.Def_DistancePreserver934_Exact_Removal
import Definitions.Def_DistancePreserver934_Exact_LoyalCore

set_option autoImplicit false
set_option maxRecDepth 2048
open Classical DistancePreserver934.Exact

private lemma radius_from_degree (n d p : ℝ) (hn : 1 ≤ n) (hp : 0 < p) (hpn : p ≤ n)
    (hd : 30*n^((1:ℝ)/5) ≤ d) :
    Eq5 d (n*d/(5*p)) (max 6 (n^((1:ℝ)/2)*d^(-(3:ℝ)/2))) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hnroot : 1 ≤ n^((1:ℝ)/5) := Real.one_le_rpow hn (by norm_num)
  have hd30 : 30 ≤ d := by nlinarith
  have hd0 : 0 < d := by linarith
  have hdp : n^((1:ℝ)/5) ≤ d/30 := by linarith
  have hc : 5 ≤ (30:ℝ)^((5:ℝ)/2) := by
    have : (30:ℝ)^ (1:ℝ) ≤ (30:ℝ)^((5:ℝ)/2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    norm_num at this ⊢
    linarith
  have hrad : n^((1:ℝ)/2)*d^(-(3:ℝ)/2) ≤ d/5 := by
    calc
      _ = (n^((1:ℝ)/5))^((5:ℝ)/2)*d^(-(3:ℝ)/2) := by
        rw [← Real.rpow_mul hn0.le]; norm_num
      _ ≤ (d/30)^((5:ℝ)/2)*d^(-(3:ℝ)/2) := by
        gcongr
      _ = d/(30:ℝ)^((5:ℝ)/2) := by
        rw [Real.div_rpow hd0.le (by norm_num)]
        calc
          _ = (d^((5:ℝ)/2)*d^(-(3:ℝ)/2))/(30:ℝ)^((5:ℝ)/2) := by ring
          _ = d/(30:ℝ)^((5:ℝ)/2) := by rw [← Real.rpow_add hd0]; norm_num
      _ ≤ d/5 := div_le_div_of_nonneg_left hd0.le (by norm_num) hc
  have hl : d/5 ≤ n*d/(5*p) := by
    apply (le_div_iff₀ (by positivity : 0 < 5*p)).mpr
    nlinarith
  refine ⟨le_max_left _ _, le_min ?_ ?_⟩
  · apply max_le
    · nlinarith
    · exact hrad.trans (by nlinarith)
  · exact (max_le (by linarith) hrad).trans hl

private lemma sec6_degree {V : Type} [Fintype V] (C : ℝ) (hC : 30 ≤ C)
    (G H : SimpleGraph V) (P : Finset (Sym2 V)) (hset : Sec6Setting C G H P) :
    1 ≤ sec6n V ∧ 0 < (P.card : ℝ) ∧ 30*(sec6n V)^((1:ℝ)/5) ≤ sec6d H := by
  let n := sec6n V
  let d := sec6d H
  have hnnonneg : 0 ≤ n := Nat.cast_nonneg _
  have hp : 0 < (P.card : ℝ) := (Real.rpow_nonneg hnnonneg _).trans_lt hset.2.2.1
  have hn : 0 < n := hp.trans_le hset.2.2.2.1
  have hn1 : 1 ≤ n := by
    have hv : 0 < Fintype.card V := by exact_mod_cast (show 0 < (Fintype.card V : ℝ) from hn)
    change 1 ≤ (Fintype.card V : ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hv)
  have hC0 : 0 ≤ C := by linarith
  have hpow : n^((6:ℝ)/5) ≤ n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
    calc
      _ = n^((8:ℝ)/9)*(n^((7:ℝ)/10))^((4:ℝ)/9) := by
        rw [← Real.rpow_mul hn.le, ← Real.rpow_add hn]; norm_num
      _ ≤ n^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn.le _)
        exact Real.rpow_le_rpow (Real.rpow_nonneg hn.le _) hset.2.2.1.le (by norm_num)
  have hviol : C*n^((6:ℝ)/5) < n*d :=
    (mul_le_mul_of_nonneg_left hpow hC0).trans_lt (by simpa only [mul_assoc] using hset.2.2.2.2)
  have hident : n^((6:ℝ)/5) = n*n^((1:ℝ)/5) := by
    conv_lhs => rw [show (6:ℝ)/5 = 1+(1:ℝ)/5 by norm_num, Real.rpow_add hn]
    rw [Real.rpow_one]
  rw [hident] at hviol
  have hdegree : C*n^((1:ℝ)/5) < d := by nlinarith
  refine ⟨hn1,hp,?_⟩
  exact (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hn.le _)).trans hdegree.le

private lemma sec6_radius {V : Type} [Fintype V] (C : ℝ) (hC : 30 ≤ C)
    (G H : SimpleGraph V) (P : Finset (Sym2 V)) (hset : Sec6Setting C G H P) :
    Eq5 (sec6d H) (sec6l H P) (sec6r H) := by
  obtain ⟨hn,hp,hd⟩ := sec6_degree C hC G H P hset
  exact radius_from_degree (sec6n V) (sec6d H) P.card hn hp hset.2.2.2.1 hd

private lemma self_minimal {V : Type} [Fintype V] (G K : SimpleGraph V)
    (R : Finset (Sym2 V)) (hK : IsMinimalPreserver G K R) : IsMinimalPreserver K K R := by
  refine ⟨⟨le_rfl, by simp⟩, ?_⟩
  intro e he hdel
  apply hK.2 e he
  exact ⟨hdel.1.trans hK.1.1, fun s t hst => (hdel.2 s t hst).trans (hK.1.2 s t hst)⟩

private lemma demand_transfer {V : Type} [Fintype V] (G K : SimpleGraph V)
    (P R : Finset (Sym2 V)) (hP : IsDemandSet G P) (hR : R ⊆ P)
    (hK : IsMinimalPreserver G K R) : IsDemandSet K R := by
  intro s t hst
  refine ⟨(hP s t (hR hst)).1, ?_⟩
  apply SimpleGraph.edist_ne_top_iff_reachable.mp
  rw [hK.1.2 s t hst]
  exact SimpleGraph.edist_ne_top_iff_reachable.mpr (hP s t (hR hst)).2

private lemma current_preserver {V : Type} [Fintype V] (G K K' : SimpleGraph V)
    (R R' : Finset (Sym2 V)) (hK : IsMinimalPreserver G K R)
    (hR : R' ⊆ R) (hup : IsUpdate G K K' R') : IsPreserver K K' R' := by
  refine ⟨hup.1, fun s t hst => ?_⟩
  rw [hup.2.1.2 s t hst, hK.1.2 s t (hR hst)]

private lemma run_inv {V : Type} [Fintype V] (c₀ c₁ c₂ : ℝ) (G H : SimpleGraph V)
    (P : Finset (Sym2 V)) (hH : IsMinimalPreserver G H P)
    (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind)
    (hrun : IsRun c₀ c₁ c₂ G H P τ st kind) :
    ∀ i ≤ τ, IsMinimalPreserver G (st i).1 (st i).2 ∧ (st i).2 ⊆ P ∧
      (st i).2.card + i ≤ P.card := by
  intro i hi
  induction i with
  | zero => simpa [hrun.1] using And.intro hH (And.intro (le_refl P) (le_refl P.card))
  | succ i ih =>
    obtain ⟨hKi,hRi,hci⟩ := ih (by omega)
    rcases hrun.2 i (by omega) with ⟨hk,hs⟩ | ⟨hk,hs⟩
    · obtain ⟨hp,q,hq,hl,hR',hup⟩ := hs
      refine ⟨hup.2, ?_, ?_⟩
      · rw [hR']
        exact (Finset.erase_subset _ _).trans hRi
      · have hc : (st (i+1)).2.card + 1 = (st i).2.card := by
          rw [hR']; exact Finset.card_erase_add_one hq
        omega
    · obtain ⟨hp,hl,Q,S,hQR,hQ,hS,hcov,hlarge,hsmall,hdiam,hR',hup⟩ := hs
      refine ⟨hup.2, ?_, ?_⟩
      · rw [hR']
        exact Finset.sdiff_subset.trans hRi
      · have hc := Finset.card_sdiff_add_card_eq_card hQR
        have hqpos := Finset.card_pos.mpr hQ
        rw [hR']
        omega

private lemma sqrt_batch (n q s D d r a b : ℝ) (hn : 0 ≤ n) (hq : 0 ≤ q)
    (hs : 0 ≤ s) (hD : 0 ≤ D) (hd : 0 < d) (hr : 0 ≤ r) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsize : s ≤ a*q/d) (hdiam : D ≤ b*r) :
    Real.sqrt (n*q*s*D) ≤ Real.sqrt (a*b)*q*Real.sqrt (n*r/d) := by
  calc
    _ ≤ Real.sqrt (n*q*(a*q/d)*(b*r)) := by gcongr
    _ = Real.sqrt ((a*b)*(q^2)*(n*r/d)) := by congr 1; ring
    _ = Real.sqrt (a*b)*q*Real.sqrt (n*r/d) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hq]

theorem solution : ∀ c₀ c₁ c₂ : ℝ, ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C →
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      Sec6Setting C G H P →
      Eq5 (sec6d H) (sec6l H P) (sec6r H) ∧
      ∀ (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind),
        IsRun c₀ c₁ c₂ G H P τ st kind → ∀ i < τ, kind i = StepKind.two →
          stepLoss st i ≤ C₂ * (sec6n V + (((st i).2 \ (st (i + 1)).2).card : ℝ) *
            Real.sqrt (sec6n V * sec6r H / sec6d H)) := by
  intro c₀ c₁ c₂
  obtain ⟨A,hA,h21⟩ := DistancePreserver934.Exact.lemma_21
  let K := Real.sqrt (max c₁ 0 * max c₂ 0)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  refine ⟨A*(1+K),by positivity,30,?_⟩
  intro C hC V inst G H P hset
  have hrad := sec6_radius C hC G H P hset
  refine ⟨hrad,?_⟩
  intro τ st kind hrun i hi hkind
  classical
  have hstate := run_inv c₀ c₁ c₂ G H P hset.2.1 τ st kind hrun
  obtain ⟨hKi,hRi,_⟩ := hstate i hi.le
  have hs : Step2 c₀ c₁ c₂ G H P (st i) (st (i+1)) := by
    rcases hrun.2 i hi with ⟨hk,hs⟩ | ⟨hk,hs⟩
    · rw [hkind] at hk; cases hk
    · exact hs
  obtain ⟨hp',hl,Q,S,hQR,hQ,hS,hcov,hlarge,hsmall,hdiam,hR',hup⟩ := hs
  have hR : IsDemandSet (st i).1 (st i).2 := demand_transfer G (st i).1 P (st i).2 hset.1 hRi hKi
  have hself := self_minimal G (st i).1 (st i).2 hKi
  obtain ⟨HQ,hHQ,hcost,hHQbound⟩ := h21 V (st i).1 (st i).2 (Fintype.card V) S Q hR hself
    le_rfl hS hQ hQR hcov hdiam.1
  have hcur : IsPreserver (st i).1 (st (i+1)).1 ((st i).2 \ Q) := by
    rw [← hR']
    exact current_preserver G (st i).1 (st (i+1)).1 (st i).2 (st (i+1)).2 hKi
      (by rw [hR']; exact Finset.sdiff_subset) hup
  have hcost' := hcost (st (i+1)).1 hcur
  have hQeq : (st i).2 \ (st (i+1)).2 = Q := by
    rw [hR']; exact Finset.sdiff_sdiff_eq_self hQR
  rw [hQeq]
  obtain ⟨hn,hp,hd⟩ := sec6_degree C hC G H P hset
  have hd0 : 0 < sec6d H := by
    have : 1 ≤ (sec6n V)^((1:ℝ)/5) := Real.one_le_rpow hn (by norm_num)
    nlinarith
  have hr0 : 0 ≤ sec6r H := le_trans (by norm_num) hrad.1
  have hSbound : (S.card : ℝ) ≤ max c₁ 0*(Q.card : ℝ)/sec6d H := by
    exact hsmall.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)) hd0.le)
  have hDbound : ((diam (st i).1 S).toNat : ℝ) ≤ max c₂ 0 * sec6r H :=
    hdiam.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hr0)
  have hsqrt := sqrt_batch (sec6n V) Q.card S.card ((diam (st i).1 S).toNat) (sec6d H)
    (sec6r H) (max c₁ 0) (max c₂ 0) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hd0 hr0 (le_max_right _ _) (le_max_right _ _) hSbound hDbound
  change Real.sqrt (sec6n V*(Q.card : ℝ)*(S.card : ℝ)*((diam (st i).1 S).toNat : ℝ)) ≤
    K*(Q.card : ℝ)*Real.sqrt (sec6n V*sec6r H/sec6d H) at hsqrt
  change (numEdges HQ : ℝ) ≤ A*(sec6n V+
    Real.sqrt (sec6n V*(Q.card : ℝ)*(S.card : ℝ)*((diam (st i).1 S).toNat : ℝ))) at hHQbound
  change stepLoss st i ≤ (numEdges HQ : ℝ) at hcost'
  calc
    _ ≤ (numEdges HQ : ℝ) := hcost'
    _ ≤ A*(sec6n V+Real.sqrt (sec6n V*(Q.card : ℝ)*(S.card : ℝ)*((diam (st i).1 S).toNat : ℝ))) := hHQbound
    _ ≤ A*(sec6n V+K*(Q.card : ℝ)*Real.sqrt (sec6n V*sec6r H/sec6d H)) := by gcongr
    _ ≤ A*(1+K)*(sec6n V+(Q.card : ℝ)*Real.sqrt (sec6n V*sec6r H/sec6d H)) := by
      have hN : 0 ≤ sec6n V := by dsimp [sec6n]; positivity
      have hQterm : 0 ≤ (Q.card : ℝ)*Real.sqrt (sec6n V*sec6r H/sec6d H) := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
      rw [mul_assoc A (1+K)]
      apply mul_le_mul_of_nonneg_left _ hA.le
      nlinarith [mul_nonneg hK hN]
