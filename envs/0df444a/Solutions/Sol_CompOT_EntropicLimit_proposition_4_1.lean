-- Prove2me | solution 1 for CompOT.EntropicLimit.proposition_4_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T01:52:34.57622+00:00
-- url     : https://prove2.me/submissions/4b33f2e7-e7f7-4b5e-81b1-0abbd5303981

-- Licensed under Apache 2.0. Full exact theorem: all three entropic-regularization convergence limits.
import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs


open scoped BigOperators
open CompOT.Assignment

namespace OTMetricProof

lemma coupling_entry_le_row {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (i : Fin n) (j : Fin m) :
    P i j ≤ a i := by
  rw [← hP.2.1 i]
  exact Finset.single_le_sum (fun k _ => hP.1 i k) (Finset.mem_univ j)

lemma coupling_entry_le_col {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (i : Fin n) (j : Fin m) :
    P i j ≤ b j := by
  rw [← hP.2.2 j]
  exact Finset.single_le_sum (fun k _ => hP.1 k j) (Finset.mem_univ i)

lemma product_coupling {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (fun i j => a i * b j) ∈ couplings a b := by
  refine ⟨fun i j => mul_nonneg (ha.1 i) (hb.1 j), ?_, ?_⟩
  · intro i
    simp only [← Finset.mul_sum, hb.2, mul_one]
  · intro j
    simp only [← Finset.sum_mul, ha.2, one_mul]

lemma coupling_nonempty {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    (couplings a b).Nonempty := ⟨_, product_coupling ha hb⟩

lemma coupling_transpose {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) :
    P.transpose ∈ couplings b a :=
  ⟨fun i j => hP.1 j i, hP.2.2, hP.2.1⟩

lemma coupling_isClosed {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    IsClosed (couplings a b) := by
  change IsClosed {P : Matrix (Fin n) (Fin m) ℝ | (∀ i j, 0 ≤ P i j) ∧
    (∀ i, ∑ j, P i j = a i) ∧ (∀ j, ∑ i, P i j = b j)}
  have h₁ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i j, 0 ≤ P i j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le (continuous_const (y := (0 : ℝ)))
        (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => P i j) by fun_prop)
  have h₂ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ i, ∑ j, P i j = a i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq
      (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => ∑ j, P i j) by fun_prop)
      continuous_const
  have h₃ : IsClosed {P : Matrix (Fin n) (Fin m) ℝ | ∀ j, ∑ i, P i j = b j} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq
      (show Continuous (fun P : Matrix (Fin n) (Fin m) ℝ => ∑ i, P i j) by fun_prop)
      continuous_const
  exact h₁.inter (h₂.inter h₃)

lemma coupling_isCompact {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (_hb : b ∈ stdSimplex ℝ (Fin m)) :
    IsCompact (couplings a b) := by
  have hbox : IsCompact (Set.Icc (0 : Fin n → Fin m → ℝ)
      (fun _ _ => (1 : ℝ))) := isCompact_Icc
  refine hbox.of_isClosed_subset (coupling_isClosed a b) ?_
  intro P hP
  show P ∈ Set.Icc (0 : Fin n → Fin m → ℝ) (fun _ _ => 1)
  exact ⟨hP.1, fun i j => (coupling_entry_le_row hP i j).trans
    (mem_Icc_of_mem_stdSimplex ha i).2⟩

end OTMetricProof


namespace EntropicLimitProof
lemma continuous_frob {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ) :
    Continuous (CompOT.Assignment.frob C) := by
  unfold CompOT.Assignment.frob
  fun_prop
end EntropicLimitProof


open Filter Topology Set
namespace EntropicLimitProof

lemma compact_regularization_zero {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {c H : X → ℝ} (hc : Continuous c) (hH : Continuous H)
    {p : X} (hp : p ∈ K) (hpmin : ∀ q ∈ K, c p ≤ c q)
    (hunique : ∀ q ∈ K, c q ≤ c p → H p ≤ H q → q = p)
    {P : ℝ → X} (hP : ∀ ε, 0 < ε → P ε ∈ K)
    (hopt : ∀ ε, 0 < ε → ∀ q ∈ K, c (P ε)-ε*H (P ε) ≤ c q-ε*H q) :
    Tendsto P (𝓝[>] (0 : ℝ)) (𝓝 p) := by
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
  apply hK.tendsto_nhds_of_unique_mapClusterPt (hpos.mono fun ε hε => hP ε hε)
  intro q hq hcluster
  obtain ⟨U,hU,hlim⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hzero : Tendsto (fun ε : ℝ => ε) (U : Filter ℝ) (𝓝 0) :=
    tendsto_id.mono_left (hU.trans inf_le_left)
  have hcost := hc.tendsto q |>.comp hlim
  have hent := hH.tendsto q |>.comp hlim
  have hineq : ∀ᶠ ε in (U : Filter ℝ), c (P ε) ≤ c p+ε*(H (P ε)-H p) := by
    filter_upwards [hpos.filter_mono hU] with ε hε
    have hh := hopt ε hε p hp
    linarith
  have hcp : c q ≤ c p := by
    have hh := le_of_tendsto_of_tendsto hcost
      (tendsto_const_nhds.add (hzero.mul (hent.sub_const (H p)))) hineq
    simpa only [zero_mul,add_zero] using hh
  have hevent : ∀ᶠ ε in (U : Filter ℝ), H p ≤ H (P ε) := by
    filter_upwards [hpos.filter_mono hU] with ε hε
    have h1 := hpmin (P ε) (hP ε hε)
    have h2 := hopt ε hε p hp
    nlinarith
  exact hunique q hq hcp (ge_of_tendsto hent hevent)

lemma compact_regularization_infinity {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {c H : X → ℝ} (hc : Continuous c) (hH : Continuous H)
    {p : X} (hp : p ∈ K) (hunique : ∀ q ∈ K, H p ≤ H q → q = p)
    {P : ℝ → X} (hP : ∀ ε, 0 < ε → P ε ∈ K)
    (hopt : ∀ ε, 0 < ε → ∀ q ∈ K, c (P ε)-ε*H (P ε) ≤ c q-ε*H q) :
    Tendsto P atTop (𝓝 p) := by
  have hpos : ∀ᶠ ε : ℝ in atTop, 0 < ε := eventually_gt_atTop 0
  apply hK.tendsto_nhds_of_unique_mapClusterPt (hpos.mono fun ε hε => hP ε hε)
  intro q hq hcluster
  obtain ⟨U,hU,hlim⟩ := mapClusterPt_iff_ultrafilter.mp hcluster
  have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (U : Filter ℝ) (𝓝 0) :=
    tendsto_inv_atTop_zero.mono_left hU
  have hcost := hc.tendsto q |>.comp hlim
  have hent := hH.tendsto q |>.comp hlim
  have hevent : ∀ᶠ ε in (U : Filter ℝ), H p-H (P ε) ≤ (c p-c (P ε))*ε⁻¹ := by
    filter_upwards [hpos.filter_mono hU] with ε hε
    have hh := hopt ε hε p hp
    rw [← div_eq_mul_inv, le_div_iff₀ hε]
    nlinarith
  have hh := le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hent)
    ((tendsto_const_nhds.sub hcost).mul hinv) hevent
  simp only [mul_zero] at hh
  exact hunique q hq (by linarith)

end EntropicLimitProof


open CompOT.Assignment CompOT.EntropicLimit
namespace EntropicLimitProof

noncomputable def midPlan {n m : ℕ} (P Q : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℝ := fun i j => (P i j+Q i j)/2

lemma entropy_continuous {n m : ℕ} : Continuous (entropy (n := n) (m := m)) := by
  unfold entropy
  fun_prop

lemma midPlan_mem {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P Q : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (hQ : Q ∈ couplings a b) :
    midPlan P Q ∈ couplings a b := by
  refine ⟨fun i j => div_nonneg (add_nonneg (hP.1 i j) (hQ.1 i j)) (by norm_num), ?_, ?_⟩
  · intro i
    simp only [midPlan, ← Finset.sum_div, Finset.sum_add_distrib, hP.2.1 i, hQ.2.1 i]
    ring
  · intro j
    simp only [midPlan, ← Finset.sum_div, Finset.sum_add_distrib, hP.2.2 j, hQ.2.2 j]
    ring

lemma frob_midPlan {n m : ℕ} (C P Q : Matrix (Fin n) (Fin m) ℝ) :
    frob C (midPlan P Q) = (frob C P+frob C Q)/2 := by
  simp only [frob, midPlan, ← mul_div_assoc, mul_add, ← Finset.sum_div, Finset.sum_add_distrib]

lemma midPlan_optimal {n m : ℕ} {C : Matrix (Fin n) (Fin m) ℝ}
    {a : Fin n → ℝ} {b : Fin m → ℝ} {P Q : Matrix (Fin n) (Fin m) ℝ}
    (hP : IsOptimalCoupling C a b P) (hQ : IsOptimalCoupling C a b Q) :
    IsOptimalCoupling C a b (midPlan P Q) := by
  refine ⟨midPlan_mem hP.1 hQ.1, fun R hR => ?_⟩
  rw [frob_midPlan]
  linarith [hP.2 R hR, hQ.2 R hR]

lemma scalar_entropy_mid_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ((Real.negMulLog x+x)+(Real.negMulLog y+y))/2 ≤
      Real.negMulLog ((x+y)/2)+(x+y)/2 := by
  have h := Real.concaveOn_negMulLog.2 hx hy
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+1/2=1)
  simp only [smul_eq_mul] at h
  have he : (1/2 : ℝ)*x+1/2*y=(x+y)/2 := by ring
  rw [he] at h
  linarith

lemma scalar_entropy_mid_lt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hne : x ≠ y) :
    ((Real.negMulLog x+x)+(Real.negMulLog y+y))/2 <
      Real.negMulLog ((x+y)/2)+(x+y)/2 := by
  have h := Real.strictConcaveOn_negMulLog.2 hx hy hne
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 1/2)
    (by norm_num : (1/2 : ℝ)+1/2=1)
  simp only [smul_eq_mul] at h
  have he : (1/2 : ℝ)*x+1/2*y=(x+y)/2 := by ring
  rw [he] at h
  linarith

lemma entropy_midPlan_lt {n m : ℕ} {P Q : Matrix (Fin n) (Fin m) ℝ}
    (hP : ∀ i j, 0 ≤ P i j) (hQ : ∀ i j, 0 ≤ Q i j) (hne : P ≠ Q) :
    (entropy P+entropy Q)/2 < entropy (midPlan P Q) := by
  classical
  have hex : ∃ i j, P i j ≠ Q i j := by
    by_contra h
    push Not at h
    exact hne (Matrix.ext fun i j => h i j)
  obtain ⟨i₀,j₀,hij⟩ := hex
  have h := Finset.sum_lt_sum
    (fun i (_ : i ∈ Finset.univ) => Finset.sum_le_sum
      (fun j (_ : j ∈ Finset.univ) => scalar_entropy_mid_le (hP i j) (hQ i j)))
    (show ∃ i ∈ Finset.univ,
      (∑ j, ((Real.negMulLog (P i j)+P i j)+(Real.negMulLog (Q i j)+Q i j))/2) <
      (∑ j, (Real.negMulLog ((P i j+Q i j)/2)+(P i j+Q i j)/2)) from
      ⟨i₀,Finset.mem_univ _,Finset.sum_lt_sum
        (fun j (_ : j ∈ Finset.univ) => scalar_entropy_mid_le (hP i₀ j) (hQ i₀ j))
        ⟨j₀,Finset.mem_univ _,scalar_entropy_mid_lt (hP i₀ j₀) (hQ i₀ j₀) hij⟩⟩)
  simpa only [entropy,midPlan,← Finset.sum_div,Finset.sum_add_distrib] using h

lemma maxEntropyOptimal_unique {n m : ℕ} {C : Matrix (Fin n) (Fin m) ℝ}
    {a : Fin n → ℝ} {b : Fin m → ℝ} {P Q : Matrix (Fin n) (Fin m) ℝ}
    (hP : IsMaxEntropyOptimal C a b P) (hQ : IsOptimalCoupling C a b Q)
    (hent : entropy P ≤ entropy Q) : Q = P := by
  by_contra hne
  have hs := entropy_midPlan_lt hP.1.1.1 hQ.1.1 (Ne.symm hne)
  have hm := hP.2 (midPlan P Q) (midPlan_optimal hP.1 hQ)
  linarith

lemma entropy_max_unique {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    {P Q : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (hQ : Q ∈ couplings a b)
    (hmax : ∀ R ∈ couplings a b, entropy R ≤ entropy P)
    (hent : entropy P ≤ entropy Q) : Q = P := by
  by_contra hne
  have hs := entropy_midPlan_lt hP.1 hQ.1 (Ne.symm hne)
  have hm := hmax (midPlan P Q) (midPlan_mem hP hQ)
  linarith

end EntropicLimitProof


namespace EntropicLimitProof

lemma scalar_entropy_tangent {x q : ℝ} (hx : 0 ≤ x) (hq : 0 < q) :
    Real.negMulLog x+x ≤ -x*Real.log q+q := by
  have hdiv : 0 ≤ x/q := div_nonneg hx hq.le
  have hb := mul_le_mul_of_nonneg_left (Real.negMulLog_le_one_sub_self hdiv) hq.le
  have he : q*(x/q)=x := mul_div_cancel₀ x hq.ne'
  have hm := Real.negMulLog_mul q (x/q)
  rw [he] at hm
  have hlog : (x/q)*Real.negMulLog q = -x*Real.log q := by
    unfold Real.negMulLog
    calc
      (x/q)*(-q*Real.log q) = -(q*(x/q))*Real.log q := by ring
      _ = -x*Real.log q := by rw [he]
  rw [hlog] at hm
  nlinarith

end EntropicLimitProof


open CompOT.Assignment CompOT.EntropicLimit OTMetricProof
namespace EntropicLimitProof

lemma entropy_entry_product_bound {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) (i : Fin n) (j : Fin m) :
    Real.negMulLog (P i j)+P i j ≤
      -(P i j)*Real.log (a i)-(P i j)*Real.log (b j)+a i*b j := by
  by_cases hq : a i*b j=0
  · have hx : P i j=0 := by
      rcases mul_eq_zero.mp hq with ha0 | hb0
      · have hu := coupling_entry_le_row hP i j
        rw [ha0] at hu
        exact le_antisymm hu (hP.1 i j)
      · have hu := coupling_entry_le_col hP i j
        rw [hb0] at hu
        exact le_antisymm hu (hP.1 i j)
    simp only [hx,Real.negMulLog_zero,zero_add,neg_zero,zero_mul,sub_zero,hq,le_refl]
  · have hpos : 0 < a i*b j := lt_of_le_of_ne (mul_nonneg (ha.1 i) (hb.1 j)) (Ne.symm hq)
    have ha0 : a i ≠ 0 := left_ne_zero_of_mul hq
    have hb0 : b j ≠ 0 := right_ne_zero_of_mul hq
    have h := scalar_entropy_tangent (hP.1 i j) hpos
    rw [Real.log_mul ha0 hb0] at h
    nlinarith

lemma entropy_product_formula {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m)) :
    entropy (Matrix.of fun i j => a i*b j) =
      (∑ i, Real.negMulLog (a i))+(∑ j, Real.negMulLog (b j))+1 := by
  simp only [entropy,Matrix.of_apply,Real.negMulLog_mul,Finset.sum_add_distrib]
  simp only [← Finset.sum_mul,← Finset.mul_sum,ha.2,hb.2,mul_one,one_mul]

lemma entropy_product_max {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    {P : Matrix (Fin n) (Fin m) ℝ} (hP : P ∈ couplings a b) :
    entropy P ≤ entropy (Matrix.of fun i j => a i*b j) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => entropy_entry_product_bound ha hb hP i j))
  have he : (∑ i, ∑ j, (-(P i j)*Real.log (a i)-(P i j)*Real.log (b j)+a i*b j)) =
      (∑ i, Real.negMulLog (a i))+(∑ j, Real.negMulLog (b j))+1 := by
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    have hrow : (∑ i, ∑ j, -(P i j)*Real.log (a i)) = ∑ i, Real.negMulLog (a i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [← Finset.sum_mul,Finset.sum_neg_distrib,hP.2.1 i,Real.negMulLog]
    have hcol : (∑ i, ∑ j, P i j*Real.log (b j)) = ∑ j, b j*Real.log (b j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul,hP.2.2 j]
    rw [hrow,hcol]
    simp only [← Finset.mul_sum,hb.2,mul_one,ha.2,Real.negMulLog,neg_mul,Finset.sum_neg_distrib]
    ring
  change entropy P ≤ _ at h
  rw [he,← entropy_product_formula ha hb] at h
  exact h

lemma product_entropy_unique {n m : ℕ} {a : Fin n → ℝ} {b : Fin m → ℝ}
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    {Q : Matrix (Fin n) (Fin m) ℝ} (hQ : Q ∈ couplings a b)
    (hent : entropy (Matrix.of fun i j => a i*b j) ≤ entropy Q) :
    Q = Matrix.of fun i j => a i*b j := by
  exact entropy_max_unique (product_coupling ha hb) hQ
    (fun _ hR => entropy_product_max ha hb hR) hent

end EntropicLimitProof


open Filter Topology
open CompOT.Assignment CompOT.EntropicLimit
namespace EntropicLimitProof

theorem native_entropic_limits {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (Pe : ℝ → Matrix (Fin n) (Fin m) ℝ)
    (hPe : ∀ ε, 0 < ε → IsEntropicOptimal C a b ε (Pe ε))
    (P₀ : Matrix (Fin n) (Fin m) ℝ) (hP₀ : IsMaxEntropyOptimal C a b P₀) :
    Tendsto Pe (𝓝[>] 0) (𝓝 P₀) ∧
      Tendsto (fun ε => entObjective C ε (Pe ε)) (𝓝[>] 0) (𝓝 (frob C P₀)) ∧
      Tendsto Pe atTop (𝓝 (Matrix.of fun i j => a i * b j)) := by
  have hc := continuous_frob C
  have hzero : Tendsto Pe (𝓝[>] 0) (𝓝 P₀) := by
    apply compact_regularization_zero (OTMetricProof.coupling_isCompact ha hb) hc
      entropy_continuous hP₀.1.1 hP₀.1.2
    · intro Q hQ hcost hent
      apply maxEntropyOptimal_unique hP₀ ⟨hQ,?_⟩ hent
      intro R hR
      exact hcost.trans (hP₀.1.2 R hR)
    · exact fun ε hε => (hPe ε hε).1
    · exact fun ε hε => (hPe ε hε).2
  refine ⟨hzero,?_,?_⟩
  · have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left inf_le_left
    have hh := (hc.tendsto P₀ |>.comp hzero).sub
      (heps.mul (entropy_continuous.tendsto P₀ |>.comp hzero))
    simpa only [zero_mul,sub_zero,entObjective,Function.comp_def] using hh
  · apply compact_regularization_infinity (OTMetricProof.coupling_isCompact ha hb) hc
      entropy_continuous (OTMetricProof.product_coupling ha hb)
    · intro Q hQ hent
      exact product_entropy_unique ha hb hQ hent
    · exact fun ε hε => (hPe ε hε).1
    · exact fun ε hε => (hPe ε hε).2

end EntropicLimitProof


namespace CompOT.EntropicLimit

open Filter Topology

/-- Proposition 4.1, pp. 425–426. Let `a ∈ Σ_n`, `b ∈ Σ_m`, `P_ε` the solution of (4.2) for
each `ε > 0`, and `P₀` the maximal-entropy optimal coupling (4.3). Then `P_ε → P₀` as
`ε → 0⁺`, `L^ε_C(a,b) = ⟨C,P_ε⟩ - ε H(P_ε) → L_C(a,b) = ⟨C,P₀⟩` as `ε → 0⁺`, and
`P_ε → a ⊗ b` as `ε → +∞` (4.4). -/
theorem proposition_4_1 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (Pe : ℝ → Matrix (Fin n) (Fin m) ℝ)
    (hPe : ∀ ε, 0 < ε → IsEntropicOptimal C a b ε (Pe ε))
    (P₀ : Matrix (Fin n) (Fin m) ℝ) (hP₀ : IsMaxEntropyOptimal C a b P₀) :
    Tendsto Pe (𝓝[>] 0) (𝓝 P₀) ∧
      Tendsto (fun ε => entObjective C ε (Pe ε)) (𝓝[>] 0) (𝓝 (CompOT.Assignment.frob C P₀)) ∧
      Tendsto Pe atTop (𝓝 (Matrix.of fun i j => a i * b j)) := by
  exact EntropicLimitProof.native_entropic_limits C a b ha hb Pe hPe P₀ hP₀

end CompOT.EntropicLimit

open CompOT.EntropicLimit

theorem solution {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (Pe : ℝ → Matrix (Fin n) (Fin m) ℝ)
    (hPe : ∀ ε, 0 < ε → IsEntropicOptimal C a b ε (Pe ε))
    (P₀ : Matrix (Fin n) (Fin m) ℝ) (hP₀ : IsMaxEntropyOptimal C a b P₀) :
    Tendsto Pe (𝓝[>] 0) (𝓝 P₀) ∧
      Tendsto (fun ε => entObjective C ε (Pe ε)) (𝓝[>] 0) (𝓝 (CompOT.Assignment.frob C P₀)) ∧
      Tendsto Pe atTop (𝓝 (Matrix.of fun i j => a i * b j)) := CompOT.EntropicLimit.proposition_4_1 C a b ha hb Pe hPe P₀ hP₀
