-- Prove2me | solution 1 for DistancePreserver934.Exact.equation_26_reachable
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:30:35.201003+00:00
-- url     : https://prove2.me/submissions/a7c5dc79-748c-4af2-9ce5-6c580e2ec1b9

import Theorems.Thm_DistancePreserver934_Exact_lemma_2
import Theorems.Thm_DistancePreserver934_Exact_lemma_10
import Theorems.Thm_DistancePreserver934_Exact_claim_22
import Theorems.Thm_DistancePreserver934_Exact_lemma_23
import Theorems.Thm_DistancePreserver934_Exact_lemma_24
import Theorems.Thm_DistancePreserver934_Exact_lemma_25

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
open Classical DistancePreserver934.Exact


private lemma private_count {V : Type} [Fintype V] (K : SimpleGraph V) (R : Finset (Sym2 V)) :
    ∑ q ∈ R, privLen K R q = (privEdges K R).card := by
  classical
  have hunion : R.biUnion (privOf K R) = privEdges K R := by
    ext e
    simp only [Finset.mem_biUnion, privOf, privEdges, Finset.mem_filter]
    constructor
    · rintro ⟨q,hq,he,hess⟩
      exact ⟨he,by rw [hess]; simp⟩
    · rintro ⟨he,hcard⟩
      obtain ⟨q,hq⟩ := Finset.card_eq_one.mp hcard
      refine ⟨q,?_,he,hq⟩
      have : q ∈ essSet K R e := by rw [hq]; simp
      exact (Finset.mem_filter.mp this).1
  have hdis : (R : Set (Sym2 V)).PairwiseDisjoint (privOf K R) := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro e he he'
    have h1 := (Finset.mem_filter.mp he).2
    have h2 := (Finset.mem_filter.mp he').2
    exact hne (Finset.singleton_injective (h1.symm.trans h2))
  simpa only [← hunion, Finset.card_biUnion hdis, privLen]

private lemma minimal_within {V : Type} [Fintype V] (G K : SimpleGraph V)
    (R R' : Finset (Sym2 V)) (hK : IsPreserver G K R) (hR : R' ⊆ R) :
    ∃ K' : SimpleGraph V, K' ≤ K ∧ IsMinimalPreserver G K' R' := by
  obtain ⟨K',⟨hpres,hsub⟩,hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun J : SimpleGraph V => IsPreserver G J R' ∧ J ≤ K)
    ⟨K,⟨hK.1,fun s t hst => hK.2 s t (hR hst)⟩,le_rfl⟩
  refine ⟨K',hsub,hpres,?_⟩
  intro e he hdel
  have hh := hmin ⟨hdel,(K'.deleteEdges_le _).trans hsub⟩ (K'.deleteEdges_le _)
  have heq : K' = K'.deleteEdges {e} := le_antisymm hh (K'.deleteEdges_le _)
  have : e ∈ (K'.deleteEdges {e}).edgeSet := heq ▸ he
  simpa [SimpleGraph.edgeSet_deleteEdges] using this

private lemma finite_descent {S : Type} (R : S → S → Prop) (μ : S → ℕ) (Inv Stop : S → Prop)
    (closed : ∀ s t, Inv s → R s t → Inv t)
    (decrease : ∀ s t, Inv s → R s t → μ t < μ s)
    (progress : ∀ s, Inv s → ¬ Stop s → ∃ t, R s t)
    (s : S) (hs : Inv s) :
    ∃ (τ : ℕ) (st : ℕ → S), st 0 = s ∧ Stop (st τ) ∧ ∀ i < τ, R (st i) (st (i+1)) := by
  classical
  generalize hk : μ s = k
  induction k using Nat.strong_induction_on generalizing s
  rename_i k ih
  by_cases hstop : Stop s
  · exact ⟨0,fun _ => s,rfl,hstop,by simp⟩
  obtain ⟨t,hrt⟩ := progress s hs hstop
  obtain ⟨τ,st,hst,hend,hsteps⟩ := ih (μ t) (by rw [← hk]; exact decrease s t hs hrt)
    t (closed s t hs hrt) rfl
  let st' : ℕ → S := fun i => if i=0 then s else st (i-1)
  refine ⟨τ+1,st',by simp [st'],?_,?_⟩
  · simpa [st'] using hend
  · intro i hi
    cases i with
    | zero => simpa [st',hst] using hrt
    | succ i => simpa [st'] using hsteps i (by omega)

private lemma numEdges_mono {V : Type} [Fintype V] {K H : SimpleGraph V} (h : K ≤ H) : numEdges K ≤ numEdges H := by
  classical
  apply Finset.card_le_card
  intro e he
  simp only [edgesF, Finset.mem_filter, Finset.mem_univ, true_and] at *
  exact SimpleGraph.edgeSet_mono h he

private lemma removal_run_exists {V : Type} [Fintype V] (c₀ c₁ c₂ C : ℝ) (hc₀ : 0 < c₀)
    (hC : 0 < C) (G H : SimpleGraph V) (P : Finset (Sym2 V))
    (hset : Sec6Setting C G H P) (hrad : Eq5 (sec6d H) (sec6l H P) (sec6r H))
    (hbatch : ∀ (K : SimpleGraph V) (R : Finset (Sym2 V)),
      Sec5Context G K R (Fintype.card V) (sec6d H) (sec6l H P) →
      sec6n V*sec6d H/20 ≤ ((privEdges K R).card : ℝ) →
      ∃ Q : Finset (Sym2 V), Q ⊆ R ∧ ∃ S : Finset V, Covers K S Q ∧
        c₀*sec6d H^2*Real.sqrt (sec6r H) ≤ (Q.card : ℝ) ∧
        (S.card : ℝ) ≤ c₁*(Q.card : ℝ)/sec6d H ∧ DiamLE K S (c₂*sec6r H)) :
    ∃ (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind),
      IsRun c₀ c₁ c₂ G H P τ st kind ∧ ((st τ).2.card : ℝ) ≤ (P.card : ℝ)/2 := by
  classical
  have hp : 0 < (P.card : ℝ) :=
    (Real.rpow_nonneg (show 0 ≤ sec6n V from Nat.cast_nonneg _) _).trans_lt hset.2.2.1
  have hn : 0 < sec6n V := hp.trans_le hset.2.2.2.1
  have hnd : 0 < sec6n V*sec6d H :=
    (mul_pos (mul_pos hC (Real.rpow_pos_of_pos hn _)) (Real.rpow_pos_of_pos hp _)).trans hset.2.2.2.2
  have hd : 0 < sec6d H := by nlinarith
  have hl : 0 < sec6l H P := div_pos hnd (by positivity)
  have hr : 0 < sec6r H := lt_of_lt_of_le (by norm_num : (0:ℝ)<6) hrad.1
  have hEid : (numEdges H : ℝ) = sec6n V*sec6d H := by
    dsimp [sec6d]
    field_simp
  let Inv : RState V → Prop := fun s => IsMinimalPreserver G s.1 s.2 ∧ s.2 ⊆ P ∧ s.1 ≤ H
  let Stop : RState V → Prop := fun s => (s.2.card : ℝ) ≤ (P.card : ℝ)/2
  let Rel : RState V → RState V → Prop := fun s t => Step1 G H P s t ∨ Step2 c₀ c₁ c₂ G H P s t
  have hclosed : ∀ s t, Inv s → Rel s t → Inv t := by
    intro s t hs hrel
    rcases hs with ⟨hmin,hsub,hgraph⟩
    rcases hrel with h1 | h2
    · obtain ⟨hp',q,hq,hlq,hR',hup⟩ := h1
      exact ⟨hup.2,by rw [hR']; exact (Finset.erase_subset _ _).trans hsub,hup.1.trans hgraph⟩
    · obtain ⟨hp',hl',Q,S,hQR,hQ,hS,hcov,hlarge,hsmall,hdiam,hR',hup⟩ := h2
      exact ⟨hup.2,by rw [hR']; exact Finset.sdiff_subset.trans hsub,hup.1.trans hgraph⟩
  have hdecrease : ∀ s t, Inv s → Rel s t → t.2.card < s.2.card := by
    intro s t hs hrel
    rcases hrel with h1 | h2
    · obtain ⟨hp',q,hq,hlq,hR',hup⟩ := h1
      rw [hR']; exact Finset.card_erase_lt_of_mem hq
    · obtain ⟨hp',hl',Q,S,hQR,hQ,hS,hcov,hlarge,hsmall,hdiam,hR',hup⟩ := h2
      rw [hR']
      have hc := Finset.card_sdiff_add_card_eq_card hQR
      have hqpos := Finset.card_pos.mpr hQ
      omega
  have hprogress : ∀ s, Inv s → ¬ Stop s → ∃ t, Rel s t := by
    intro s hs hstop
    have hhalf : (P.card : ℝ)/2 < (s.2.card : ℝ) := lt_of_not_ge hstop
    obtain ⟨hmin,hsub,hgraph⟩ := hs
    by_cases hsmall : ∃ q ∈ s.2, (privLen s.1 s.2 q : ℝ) ≤ sec6l H P
    · obtain ⟨q,hq,hlq⟩ := hsmall
      obtain ⟨K',hK',hmin'⟩ := minimal_within G s.1 s.2 (s.2.erase q) hmin.1 (Finset.erase_subset _ _)
      refine ⟨(K',s.2.erase q),Or.inl ?_⟩
      exact ⟨hhalf,q,hq,hlq,rfl,hK',hmin'⟩
    · have hlong : ∀ q ∈ s.2, sec6l H P < (privLen s.1 s.2 q : ℝ) := by
        push_neg at hsmall
        exact hsmall
      have hctx : Sec5Context G s.1 s.2 (Fintype.card V) (sec6d H) (sec6l H P) := by
        refine ⟨fun u v huv => hset.1 u v (hsub huv),hmin,le_rfl,?_,fun q hq => (hlong q hq).le⟩
        exact (show (numEdges s.1 : ℝ) ≤ (numEdges H : ℝ) by exact_mod_cast numEdges_mono hgraph).trans_eq hEid
      have hmass : sec6n V*sec6d H/20 ≤ ((privEdges s.1 s.2).card : ℝ) := by
        have hsum : (s.2.card : ℝ)*sec6l H P ≤ ((privEdges s.1 s.2).card : ℝ) := by
          have hle := Finset.sum_le_sum (s := s.2) (fun q hq => (hlong q hq).le)
          have hcast : (∑ q ∈ s.2, (privLen s.1 s.2 q : ℝ)) = ((privEdges s.1 s.2).card : ℝ) := by
            exact_mod_cast private_count s.1 s.2
          simpa only [Finset.sum_const, nsmul_eq_mul, hcast] using hle
        have hhalfprod := mul_lt_mul_of_pos_right hhalf hl
        have hid : (P.card : ℝ)/2*sec6l H P = sec6n V*sec6d H/10 := by
          dsimp [sec6l]
          field_simp
          ring
        rw [hid] at hhalfprod
        linarith
      obtain ⟨Q,hQR,S,hcov,hlarge,hsmall',hdiam⟩ := hbatch s.1 s.2 hctx hmass
      have hQ : Q.Nonempty := by
        apply Finset.card_pos.mp
        have hpos : 0 < (Q.card : ℝ) := (mul_pos (mul_pos hc₀ (sq_pos_of_pos hd)) (Real.sqrt_pos.mpr hr)).trans_le hlarge
        exact_mod_cast hpos
      have hS : S.Nonempty := by
        obtain ⟨q,hq⟩ := hQ
        obtain ⟨x,hx,_⟩ := hcov q hq
        exact ⟨x,hx⟩
      obtain ⟨K',hK',hmin'⟩ := minimal_within G s.1 s.2 (s.2 \ Q) hmin.1 Finset.sdiff_subset
      refine ⟨(K',s.2 \ Q),Or.inr ?_⟩
      exact ⟨hhalf,hlong,Q,S,hQR,hQ,hS,hcov,hlarge,hsmall',hdiam,rfl,hK',hmin'⟩
  obtain ⟨τ,st,hstart,hstop,hsteps⟩ := finite_descent Rel (fun s => s.2.card) Inv Stop
    hclosed hdecrease hprogress (H,P) ⟨hset.2.1,le_rfl,le_rfl⟩
  let kind : ℕ → StepKind := fun i => if Step1 G H P (st i) (st (i+1)) then .one else .two
  refine ⟨τ,st,kind,⟨hstart,?_⟩,hstop⟩
  intro i hi
  rcases hsteps i hi with h1 | h2
  · exact Or.inl ⟨by simp [kind,h1],h1⟩
  · by_cases h1 : Step1 G H P (st i) (st (i+1))
    · exact Or.inl ⟨by simp [kind,h1],h1⟩
    · exact Or.inr ⟨by simp [kind,h1],h2⟩

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


private lemma base_scale (n p : ℝ) (hn : 1 ≤ n) (hp : 0 ≤ p)
    (hlo : n^((1:ℝ)/4) ≤ p) (hhi : p ≤ n^((7:ℝ)/10)) :
    n ≤ n^((8:ℝ)/9)*p^((4:ℝ)/9) ∧ n^((1:ℝ)/2)*p ≤ n^((8:ℝ)/9)*p^((4:ℝ)/9) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hp0 : 0 < p := (Real.rpow_pos_of_pos hn0 _).trans_le hlo
  constructor
  · calc
      n = n^((8:ℝ)/9)*(n^((1:ℝ)/4))^((4:ℝ)/9) := by
        rw [← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]; norm_num
      _ ≤ n^((8:ℝ)/9)*p^((4:ℝ)/9) := by
        gcongr
  · have hpow : p^((5:ℝ)/9) ≤ n^((7:ℝ)/18) := by
      have h := Real.rpow_le_rpow hp hhi (by norm_num : (0:ℝ)≤5/9)
      simpa only [← Real.rpow_mul hn0.le, show ((7:ℝ)/10)*(5/9)=7/18 by norm_num] using h
    have hpident : p = p^((4:ℝ)/9)*p^((5:ℝ)/9) := by
      rw [← Real.rpow_add hp0]; norm_num
    calc
      _ = p^((4:ℝ)/9)*(n^((1:ℝ)/2)*p^((5:ℝ)/9)) := by
        conv_lhs => rw [hpident]
        ring
      _ ≤ p^((4:ℝ)/9)*(n^((1:ℝ)/2)*n^((7:ℝ)/18)) := by gcongr
      _ = _ := by rw [← Real.rpow_add hn0]; norm_num; ring

private lemma half_factor : (4:ℝ)/3 < (2:ℝ)^((4:ℝ)/9) := by
  apply (Real.rpow_lt_rpow_iff (by norm_num : (0:ℝ)≤4/3)
    (Real.rpow_nonneg (by norm_num) _) (by norm_num : (0:ℝ)<9)).mp
  rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  norm_num

private lemma half_scale (n p : ℝ) (hn : 0 ≤ n) (hp : 0 ≤ p) :
    n^((8:ℝ)/9)*(p/2)^((4:ℝ)/9) =
      (n^((8:ℝ)/9)*p^((4:ℝ)/9))/(2:ℝ)^((4:ℝ)/9) := by
  rw [Real.div_rpow hp (by norm_num)]
  ring

private lemma run_loss_identity {V : Type} [Fintype V] (c₀ c₁ c₂ : ℝ) (G H : SimpleGraph V)
    (P : Finset (Sym2 V)) (τ : ℕ) (st : ℕ → RState V) (kind : ℕ → StepKind)
    (hrun : IsRun c₀ c₁ c₂ G H P τ st kind) :
    kindLoss τ st kind .one + kindLoss τ st kind .two =
      (numEdges H : ℝ)-(numEdges (st τ).1 : ℝ) := by
  calc
    _ = ∑ i ∈ Finset.range τ, stepLoss st i := by
      simp only [kindLoss, Finset.sum_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      cases kind i <;> simp
    _ = (numEdges (st 0).1 : ℝ)-(numEdges (st τ).1 : ℝ) := by
      exact Finset.sum_range_sub' _ _
    _ = _ := by rw [hrun.1]

theorem solution : ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      IsDemandSet G P →
      (Fintype.card V : ℝ)^((1:ℝ)/4) ≤ (P.card : ℝ) → (P.card : ℝ) ≤ (Fintype.card V : ℝ) →
      IsMinimalPreserver G H P →
      (numEdges H : ℝ) ≤ C*(Fintype.card V : ℝ)^((8:ℝ)/9)*(P.card : ℝ)^((4:ℝ)/9) := by
  obtain ⟨CCE,hCCE,hCE⟩ := DistancePreserver934.Exact.lemma_2
  obtain ⟨c₀,c₁,c₂,hc₀,h10⟩ := DistancePreserver934.Exact.lemma_10
  obtain ⟨A,hA,C24,h24⟩ := DistancePreserver934.Exact.lemma_24 c₀ c₁ c₂
  obtain ⟨C25,h25⟩ := DistancePreserver934.Exact.lemma_25 c₀ c₁ c₂ hc₀
  let C := max 30 (max ((2:ℝ)^((13:ℝ)/9)*CCE) (max C24 C25))
  have hC30 : 30 ≤ C := le_max_left _ _
  have hCpos : 0 < C := by linarith
  have hC13 : (2:ℝ)^((13:ℝ)/9)*CCE ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC24 : C24 ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC25 : C25 ≤ C := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC2 : 2*CCE ≤ C := by
    have hpow : (2:ℝ) ≤ (2:ℝ)^((13:ℝ)/9) := by
      calc
        (2:ℝ) = (2:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    exact (mul_le_mul_of_nonneg_right hpow hCCE.le).trans hC13
  refine ⟨C,hCpos,?_⟩
  have hbound : ∀ p : ℕ, ∀ (V : Type) [Fintype V] (G H : SimpleGraph V) (P : Finset (Sym2 V)),
      P.card = p → IsDemandSet G P →
      (Fintype.card V : ℝ)^((1:ℝ)/4) ≤ (p : ℝ) → (p : ℝ) ≤ (Fintype.card V : ℝ) →
      IsMinimalPreserver G H P →
      (numEdges H : ℝ) ≤ C*(Fintype.card V : ℝ)^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9) := by
    intro p
    induction p using Nat.strong_induction_on
    rename_i p ih
    intro V inst G H P hpc hR hlo hhi hH
    classical
    by_cases hz : Fintype.card V = 0
    · have h := hCE V G H P hR hH
      simpa [hz,Real.zero_rpow] using h
    let n : ℝ := Fintype.card V
    have hn1 : 1 ≤ n := by
      change 1 ≤ (Fintype.card V : ℝ)
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
    have hn : 0 < n := lt_of_lt_of_le zero_lt_one hn1
    have hp : 0 < (p : ℝ) := (Real.rpow_pos_of_pos hn _).trans_le hlo
    by_cases hbase : (p : ℝ) ≤ n^((7:ℝ)/10)
    · have hb := base_scale n p hn1 hp.le hlo hbase
      have hclassic := hCE V G H P hR hH
      rw [hpc,Real.sqrt_eq_rpow] at hclassic
      change (numEdges H : ℝ) ≤ CCE*(n+(p : ℝ)*n^((1:ℝ)/2)) at hclassic
      have hT : 0 ≤ n^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9) := by positivity
      calc
        _ ≤ CCE*(n+(p : ℝ)*n^((1:ℝ)/2)) := hclassic
        _ ≤ (2*CCE)*(n^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9)) := by
          nlinarith [mul_le_mul_of_nonneg_left hb.1 hCCE.le,mul_le_mul_of_nonneg_left hb.2 hCCE.le]
        _ ≤ C*(n^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9)) := mul_le_mul_of_nonneg_right hC2 hT
        _ = _ := by ring
    have hhigh : n^((7:ℝ)/10) < (p : ℝ) := lt_of_not_ge hbase
    by_contra! hviol
    have hEid : (numEdges H : ℝ) = sec6n V*sec6d H := by
      have hnsec : sec6n V ≠ 0 := ne_of_gt hn
      dsimp [sec6d]
      field_simp [hnsec]
    have hset : Sec6Setting C G H P := by
      refine ⟨hR,hH,?_,?_,?_⟩
      · simpa only [hpc,sec6n,n] using hhigh
      · simpa only [hpc,sec6n,n] using hhi
      · rw [← hEid,hpc]
        exact hviol
    have hrad := (h24 C hC24 V G H P hset).1
    have hV0 : 0 < Fintype.card V := Nat.pos_of_ne_zero hz
    obtain ⟨τ,st,kind,hrun,hstop⟩ := removal_run_exists c₀ c₁ c₂ C hc₀ hCpos G H P hset hrad
      (fun K R hctx hmass => h10 V G K R (Fintype.card V) (sec6d H) (sec6l H P) (sec6r H) hV0 hctx hmass hrad)
    have hstate := run_inv c₀ c₁ c₂ G H P hH τ st kind hrun
    obtain ⟨hJ,hsub,hcard⟩ := hstate τ le_rfl
    have hJR : IsDemandSet G (st τ).2 := fun u v huv => hR u v (hsub huv)
    have hCE' : ∀ (G' J : SimpleGraph V) (T : Finset (Sym2 V)),
        IsDemandSet G' T → IsMinimalPreserver G' J T →
        (numEdges J : ℝ) ≤ CCE*(n+n^((1:ℝ)/2)*(T.card : ℝ)) := by
      intro G' J T hT hJ
      simpa only [Real.sqrt_eq_rpow,mul_comm] using hCE V G' J T hT hJ
    have hIH : ∀ (G' J : SimpleGraph V) (T : Finset (Sym2 V)),
        IsDemandSet G' T → n^((1:ℝ)/4) ≤ (T.card : ℝ) → T.card < p →
        IsMinimalPreserver G' J T →
        (numEdges J : ℝ) ≤ C*n^((8:ℝ)/9)*(T.card : ℝ)^((4:ℝ)/9) := by
      intro G' J T hT hlo' hlt hJ'
      apply ih T.card hlt V G' J T rfl hT hlo' _ hJ'
      exact (show (T.card : ℝ) ≤ p by exact_mod_cast hlt.le).trans hhi
    have hres := DistancePreserver934.Exact.claim_22 G p C CCE hhigh hhi hCE' hC13 hIH
      (st τ).2 (st τ).1 hJR (by simpa only [hpc] using hstop) hJ
    have h1 := DistancePreserver934.Exact.lemma_23 c₀ c₁ c₂ C G H P hset τ st kind hrun
    have h2 := h25 C hC25 V G H P hset τ st kind hrun
    have hloss := run_loss_identity c₀ c₁ c₂ G H P τ st kind hrun
    have hretain : 3*(numEdges H : ℝ)/4 ≤ (numEdges (st τ).1 : ℝ) := by
      rw [← hEid] at h1 h2
      linarith
    change (numEdges (st τ).1 : ℝ) ≤ C*n^((8:ℝ)/9)*((p:ℝ)/2)^((4:ℝ)/9) at hres
    rw [mul_assoc,half_scale n p hn.le hp.le] at hres
    have hβ : 0 < (2:ℝ)^((4:ℝ)/9) := Real.rpow_pos_of_pos (by norm_num) _
    have hT : 0 < C*n^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9) := by positivity
    have hres' : (numEdges (st τ).1 : ℝ) ≤
        (C*n^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9))/(2:ℝ)^((4:ℝ)/9) := by
      simpa only [mul_div_assoc,mul_assoc] using hres
    have hstrict : (C*n^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9))/(2:ℝ)^((4:ℝ)/9) <
        3*(C*n^((8:ℝ)/9)*(p : ℝ)^((4:ℝ)/9))/4 := by
      apply (div_lt_iff₀ hβ).mpr
      nlinarith [mul_pos hT (sub_pos.mpr half_factor)]
    nlinarith
  intro V inst G H P hR hlo hhi hH
  exact hbound P.card V G H P rfl hR hlo hhi hH
