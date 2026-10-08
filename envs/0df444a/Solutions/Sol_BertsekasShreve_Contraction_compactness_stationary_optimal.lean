-- Prove2me | solution 1 for BertsekasShreve.Contraction.compactness_stationary_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:38:32.620271+00:00
-- url     : https://prove2.me/submissions/f84773b5-540c-4986-89b1-84649578a3d6

import Mathlib
import Definitions.Def_BertsekasShreve_Contraction_Model
import Definitions.Def_BertsekasShreve_Contraction_AssumptionC

open Filter Topology

namespace BertsekasShreve.Contraction

section Basics
variable {S : Type*}

lemma bs_toF_injective : Function.Injective (toF (S := S)) := by
  intro J J' h
  apply lp.ext
  funext x
  have := congrFun h x
  simpa [toF] using this

lemma bs_abs_le_norm (A B : BFun S) (x : S) : |A x - B x| ≤ ‖A - B‖ := by
  have := lp.norm_apply_le_norm (p := ⊤) (by simp) (A - B) x
  simpa [Real.norm_eq_abs] using this

lemma bs_norm_le (A B : BFun S) (c : ℝ) (hc : 0 ≤ c) (h : ∀ x, |A x - B x| ≤ c) :
    ‖A - B‖ ≤ c := by
  apply lp.norm_le_of_forall_le hc
  intro x
  simpa [Real.norm_eq_abs] using h x

lemma bs_supDist_iff (A B : BFun S) (c : ℝ) :
    SupDistLe (toF A) (toF B) c ↔ ∀ x, |A x - B x| ≤ c := by
  constructor
  · intro h x
    obtain ⟨a, b, ha, hb, hab⟩ := h x
    simp only [toF, EReal.coe_eq_coe_iff] at ha hb
    rw [ha, hb]; exact hab
  · intro h x
    exact ⟨A x, B x, rfl, rfl, h x⟩

lemma bs_supDist_norm (A B : BFun S) : SupDistLe (toF A) (toF B) ‖A - B‖ :=
  (bs_supDist_iff A B _).2 (bs_abs_le_norm A B)

lemma bs_ereal_le_of_eps (a : EReal) (t : ℝ) (h : ∀ ε : ℝ, 0 < ε → a ≤ ((t + ε : ℝ) : EReal)) :
    a ≤ (t : EReal) := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨r, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have h1' : t < r := EReal.coe_lt_coe_iff.1 h1
  have := h (r - t) (by linarith)
  have : a ≤ (r : EReal) := by simpa using this
  exact absurd (lt_of_lt_of_le h2 this) (lt_irrefl _)

/-- generic fixed point lemma for maps whose m-th iterate contracts on a closed set -/
lemma bs_fp_gen (Bbar : Set (BFun S)) (hcl : IsClosed Bbar) (hne : Bbar.Nonempty)
    (F : BFun S → BFun S) (hF : ∀ J ∈ Bbar, F J ∈ Bbar) (m : ℕ) (hm : 0 < m) (ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hc : ∀ J ∈ Bbar, ∀ J' ∈ Bbar, ‖F^[m] J - F^[m] J'‖ ≤ ρ * ‖J - J'‖) :
    ∃ Jf ∈ Bbar, F Jf = Jf ∧ (∀ J ∈ Bbar, F J = J → J = Jf) ∧
      (∀ J ∈ Bbar, Tendsto (fun N => F^[N] J) atTop (𝓝 Jf)) ∧
      (∀ J ∈ Bbar, ‖J - Jf‖ * (1 - ρ) ≤ ‖F^[m] J - J‖) := by
  have hiter : ∀ k, ∀ J ∈ Bbar, F^[k] J ∈ Bbar := by
    intro k; induction k with
    | zero => intro J hJ; simpa using hJ
    | succ k ih => intro J hJ; rw [Function.iterate_succ_apply]; exact ih _ (hF J hJ)
  have : CompleteSpace Bbar := hcl.completeSpace_coe
  have : Nonempty Bbar := ⟨⟨hne.some, hne.some_mem⟩⟩
  let G : Bbar → Bbar := fun J => ⟨F^[m] J, hiter m J J.2⟩
  have hG : ContractingWith ⟨ρ, hρ0⟩ G := by
    refine ⟨by exact_mod_cast hρ1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm, G, NNReal.coe_mk]
    exact hc a a.2 b b.2
  set Jf : Bbar := ContractingWith.fixedPoint G hG with hJfdef
  have hfix : F^[m] Jf.1 = Jf.1 := by
    have := ContractingWith.fixedPoint_isFixedPt (f := G) hG
    exact congrArg Subtype.val this
  -- uniqueness among F^m fixed points
  have uniq : ∀ J ∈ Bbar, F^[m] J = J → J = Jf.1 := by
    intro J hJ hJf
    have h := hc J hJ Jf.1 Jf.2
    rw [hJf, hfix] at h
    have h0 : ‖J - Jf.1‖ = 0 := by
      have := norm_nonneg (J - Jf.1); nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h0)
  have hFfix : F Jf.1 = Jf.1 := by
    apply uniq _ (hF _ Jf.2)
    rw [← Function.iterate_succ_apply F m, Function.iterate_succ_apply', hfix]
  refine ⟨Jf.1, Jf.2, hFfix, ?_, ?_, ?_⟩
  · intro J hJ hJF
    apply uniq J hJ
    exact Function.iterate_fixed hJF m
  · intro J hJ
    have hk : ∀ k, ∀ K ∈ Bbar, ‖F^[m * k] K - Jf.1‖ ≤ ρ ^ k * ‖K - Jf.1‖ := by
      intro k; induction k with
      | zero => intro K hK; simp
      | succ k ih =>
        intro K hK
        rw [Nat.mul_succ, add_comm, Function.iterate_add_apply]
        have h1 := hc (F^[m * k] K) (hiter _ K hK) Jf.1 Jf.2
        rw [hfix] at h1
        calc ‖F^[m] (F^[m * k] K) - Jf.1‖ ≤ ρ * ‖F^[m * k] K - Jf.1‖ := h1
          _ ≤ ρ * (ρ ^ k * ‖K - Jf.1‖) := mul_le_mul_of_nonneg_left (ih K hK) hρ0
          _ = ρ ^ (k + 1) * ‖K - Jf.1‖ := by ring
    set M := ∑ r ∈ Finset.range m, ‖F^[r] J - Jf.1‖ with hM
    have hbound : ∀ N, ‖F^[N] J - Jf.1‖ ≤ ρ ^ (N / m) * M := by
      intro N
      have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
      rw [hN, Function.iterate_add_apply]
      rw [← hN]
      calc _ ≤ ρ ^ (N / m) * ‖F^[N % m] J - Jf.1‖ := hk _ _ (hiter _ J hJ)
        _ ≤ ρ ^ (N / m) * M := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hρ0 _)
          exact Finset.single_le_sum (f := fun r => ‖F^[r] J - Jf.1‖)
            (fun r _ => norm_nonneg _) (Finset.mem_range.2 (Nat.mod_lt N hm))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    apply squeeze_zero (fun N => norm_nonneg _) hbound
    have h1 : Tendsto (fun N : ℕ => ρ ^ (N / m)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
        (Nat.tendsto_div_const_atTop hm.ne')
    simpa using h1.mul_const M
  · intro J hJ
    have h1 := hc J hJ Jf.1 Jf.2
    rw [hfix] at h1
    have h2 : ‖J - Jf.1‖ ≤ ‖J - F^[m] J‖ + ‖F^[m] J - Jf.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h3 : ‖J - F^[m] J‖ = ‖F^[m] J - J‖ := norm_sub_rev _ _
    nlinarith

end Basics


section ModelPart
variable {S C : Type*} {P : Model S C} {Bbar : Set (BFun S)} {m : ℕ} {ρ α : ℝ}

open Classical in
noncomputable def bs_tm (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J : BFun S) : BFun S :=
  if h : J ∈ Bbar then Classical.choose (hC.Tmu_mem μ J h) else J

lemma bs_tm_spec (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J : BFun S) (hJ : J ∈ Bbar) :
    bs_tm hC μ J ∈ Bbar ∧ toF (bs_tm hC μ J) = P.Tmu μ (toF J) := by
  unfold bs_tm; rw [dif_pos hJ]
  exact ⟨(Classical.choose_spec (hC.Tmu_mem μ J hJ)).1,
    (Classical.choose_spec (hC.Tmu_mem μ J hJ)).2.symm⟩

open Classical in
noncomputable def bs_tb (hC : AssumptionC P Bbar m ρ α) (J : BFun S) : BFun S :=
  if h : J ∈ Bbar then Classical.choose (hC.T_mem J h) else J

lemma bs_tb_spec (hC : AssumptionC P Bbar m ρ α) (J : BFun S) (hJ : J ∈ Bbar) :
    bs_tb hC J ∈ Bbar ∧ toF (bs_tb hC J) = P.T (toF J) := by
  unfold bs_tb; rw [dif_pos hJ]
  exact ⟨(Classical.choose_spec (hC.T_mem J hJ)).1,
    (Classical.choose_spec (hC.T_mem J hJ)).2.symm⟩

lemma bs_tm_apply (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J : BFun S) (hJ : J ∈ Bbar)
    (x : S) : ((bs_tm hC μ J x : ℝ) : EReal) = P.H x (μ.1 x) (toF J) :=
  congrFun (bs_tm_spec hC μ J hJ).2 x

lemma bs_tb_apply (hC : AssumptionC P Bbar m ρ α) (J : BFun S) (hJ : J ∈ Bbar)
    (x : S) : ((bs_tb hC J x : ℝ) : EReal) = ⨅ u ∈ P.U x, P.H x u (toF J) :=
  congrFun (bs_tb_spec hC J hJ).2 x

lemma bs_tm_lip (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) : ‖bs_tm hC μ J - bs_tm hC μ J'‖ ≤ α * ‖J - J'‖ := by
  have h := hC.lipschitz μ J J'
  rw [← (bs_tm_spec hC μ J hJ).2, ← (bs_tm_spec hC μ J' hJ').2, bs_supDist_iff] at h
  exact bs_norm_le _ _ _ (mul_nonneg hC.α_pos.le (norm_nonneg _)) h

lemma bs_tm_mono (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) (h : ∀ x, J x ≤ J' x) (x : S) : bs_tm hC μ J x ≤ bs_tm hC μ J' x := by
  have := P.mono x (μ.1 x) (μ.2 x) (toF J) (toF J') (fun y => EReal.coe_le_coe_iff.2 (h y))
  rw [← bs_tm_apply hC μ J hJ, ← bs_tm_apply hC μ J' hJ'] at this
  exact EReal.coe_le_coe_iff.1 this

lemma bs_tb_le (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J : BFun S) (hJ : J ∈ Bbar)
    (x : S) : bs_tb hC J x ≤ bs_tm hC μ J x := by
  have : (⨅ u ∈ P.U x, P.H x u (toF J)) ≤ P.H x (μ.1 x) (toF J) := iInf₂_le (μ.1 x) (μ.2 x)
  rw [← bs_tm_apply hC μ J hJ, ← bs_tb_apply hC J hJ] at this
  exact EReal.coe_le_coe_iff.1 this

lemma bs_tb_mono (hC : AssumptionC P Bbar m ρ α) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) (h : ∀ x, J x ≤ J' x) (x : S) : bs_tb hC J x ≤ bs_tb hC J' x := by
  have : (⨅ u ∈ P.U x, P.H x u (toF J)) ≤ (⨅ u ∈ P.U x, P.H x u (toF J')) :=
    iInf₂_mono fun u hu => P.mono x u hu (toF J) (toF J') (fun y => EReal.coe_le_coe_iff.2 (h y))
  rw [← bs_tb_apply hC J hJ, ← bs_tb_apply hC J' hJ'] at this
  exact EReal.coe_le_coe_iff.1 this

lemma bs_tb_approx (hC : AssumptionC P Bbar m ρ α) (J : BFun S) (hJ : J ∈ Bbar) (ε : ℝ)
    (hε : 0 < ε) : ∃ μ : P.Selector, ∀ x, bs_tm hC μ J x ≤ bs_tb hC J x + ε := by
  have key : ∀ x, ∃ u, ∃ hu : u ∈ P.U x, P.H x u (toF J) < ((bs_tb hC J x + ε : ℝ) : EReal) := by
    intro x
    have h1 : ((bs_tb hC J x : ℝ) : EReal) < ((bs_tb hC J x + ε : ℝ) : EReal) :=
      EReal.coe_lt_coe_iff.2 (by linarith)
    rw [bs_tb_apply hC J hJ] at h1
    obtain ⟨u, hu⟩ := iInf_lt_iff.1 h1
    obtain ⟨hu', hu''⟩ := iInf_lt_iff.1 hu
    exact ⟨u, hu', hu''⟩
  choose u hu hlt using key
  refine ⟨⟨u, hu⟩, fun x => ?_⟩
  have e := bs_tm_apply hC ⟨u, hu⟩ J hJ x
  exact (EReal.coe_lt_coe_iff.1 (lt_of_eq_of_lt e (hlt x))).le

noncomputable def bs_cp (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) : ℕ → BFun S → BFun S
  | 0, J => J
  | N + 1, J => bs_cp hC π N (bs_tm hC (π N) J)

lemma bs_cp_spec (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (N : ℕ) :
    ∀ J ∈ Bbar, bs_cp hC π N J ∈ Bbar ∧ toF (bs_cp hC π N J) = P.comp π N (toF J) := by
  induction N with
  | zero => intro J hJ; exact ⟨hJ, rfl⟩
  | succ N ih =>
    intro J hJ
    have h1 := bs_tm_spec hC (π N) J hJ
    have h2 := ih _ h1.1
    refine ⟨h2.1, ?_⟩
    show toF (bs_cp hC π N (bs_tm hC (π N) J)) = P.comp π N (P.Tmu (π N) (toF J))
    rw [h2.2, h1.2]

lemma bs_cp_add (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (a b : ℕ) :
    ∀ J, bs_cp hC π (a + b) J = bs_cp hC π a (bs_cp hC (fun n => π (a + n)) b J) := by
  induction b with
  | zero => intro J; rfl
  | succ b ih =>
    intro J
    show bs_cp hC π (a + b) (bs_tm hC (π (a + b)) J) =
      bs_cp hC π a (bs_cp hC (fun n => π (a + n)) (b + 1) J)
    rw [ih]; rfl

lemma bs_cp_succ' (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (k : ℕ) (J : BFun S) :
    bs_cp hC π (k + 1) J = bs_tm hC (π 0) (bs_cp hC (fun n => π (n + 1)) k J) := by
  rw [show k + 1 = 1 + k from add_comm _ _, bs_cp_add]
  show bs_tm hC (π 0) _ = _
  congr 2
  funext n; rw [add_comm]

lemma bs_cp_lip (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (k : ℕ) :
    ∀ J ∈ Bbar, ∀ J' ∈ Bbar, ‖bs_cp hC π k J - bs_cp hC π k J'‖ ≤ α ^ k * ‖J - J'‖ := by
  induction k with
  | zero => intro J _ J' _; simp [bs_cp]
  | succ k ih =>
    intro J hJ J' hJ'
    show ‖bs_cp hC π k (bs_tm hC (π k) J) - bs_cp hC π k (bs_tm hC (π k) J')‖ ≤ _
    calc _ ≤ α ^ k * ‖bs_tm hC (π k) J - bs_tm hC (π k) J'‖ :=
          ih _ (bs_tm_spec hC _ J hJ).1 _ (bs_tm_spec hC _ J' hJ').1
      _ ≤ α ^ k * (α * ‖J - J'‖) :=
          mul_le_mul_of_nonneg_left (bs_tm_lip hC _ J J' hJ hJ') (pow_nonneg hC.α_pos.le _)
      _ = α ^ (k + 1) * ‖J - J'‖ := by ring

lemma bs_cp_mono (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (k : ℕ) :
    ∀ J ∈ Bbar, ∀ J' ∈ Bbar, (∀ x, J x ≤ J' x) → ∀ x, bs_cp hC π k J x ≤ bs_cp hC π k J' x := by
  induction k with
  | zero => intro J _ J' _ h; exact h
  | succ k ih =>
    intro J hJ J' hJ' h
    exact ih _ (bs_tm_spec hC _ J hJ).1 _ (bs_tm_spec hC _ J' hJ').1
      (bs_tm_mono hC _ J J' hJ hJ' h)

lemma bs_cp_contr (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) : ‖bs_cp hC π m J - bs_cp hC π m J'‖ ≤ ρ * ‖J - J'‖ := by
  have h := hC.contraction π J hJ J' hJ'
  rw [← (bs_cp_spec hC π m J hJ).2, ← (bs_cp_spec hC π m J' hJ').2, bs_supDist_iff] at h
  exact bs_norm_le _ _ _ (mul_nonneg hC.ρ_pos.le (norm_nonneg _)) h

lemma bs_cp_stat (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (N : ℕ) :
    ∀ J, bs_cp hC (P.stationary μ) N J = (bs_tm hC μ)^[N] J := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show bs_cp hC (P.stationary μ) N (bs_tm hC μ J) = _
    rw [ih, Function.iterate_succ_apply]

lemma bs_default_policy (P : Model S C) : Nonempty P.Policy :=
  ⟨fun _ => ⟨fun x => (P.U_nonempty x).some, fun x => (P.U_nonempty x).some_mem⟩⟩

lemma bs_tbi_spec (hC : AssumptionC P Bbar m ρ α) (k : ℕ) :
    ∀ J ∈ Bbar, (bs_tb hC)^[k] J ∈ Bbar ∧ toF ((bs_tb hC)^[k] J) = P.T^[k] (toF J) := by
  induction k with
  | zero => intro J hJ; exact ⟨hJ, rfl⟩
  | succ k ih =>
    intro J hJ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := ih J hJ
    have h2 := bs_tb_spec hC _ h1.1
    exact ⟨h2.1, by rw [h2.2, h1.2]⟩

lemma bs_tbi_le (hC : AssumptionC P Bbar m ρ α) (J : BFun S) (hJ : J ∈ Bbar) (k : ℕ) :
    ∀ (π : P.Policy) x, (bs_tb hC)^[k] J x ≤ bs_cp hC π k J x := by
  induction k with
  | zero => intro π x; exact le_rfl
  | succ k ih =>
    intro π x
    rw [Function.iterate_succ_apply', bs_cp_succ']
    have hm1 := (bs_tbi_spec hC k J hJ).1
    have hm2 := (bs_cp_spec hC (fun n => π (n + 1)) k J hJ).1
    calc _ ≤ bs_tb hC (bs_cp hC (fun n => π (n + 1)) k J) x :=
          bs_tb_mono hC _ _ hm1 hm2 (ih _) x
      _ ≤ _ := bs_tb_le hC _ _ hm2 x

lemma bs_tbi_approx (hC : AssumptionC P Bbar m ρ α) (J : BFun S) (hJ : J ∈ Bbar) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ π : P.Policy, ∀ x, bs_cp hC π k J x ≤ (bs_tb hC)^[k] J x + ε := by
  induction k with
  | zero =>
    intro ε hε
    obtain ⟨π⟩ := bs_default_policy P
    exact ⟨π, fun x => by show J x ≤ J x + ε; linarith⟩
  | succ k ih =>
    intro ε hε
    have hα := hC.α_pos
    obtain ⟨π', hπ'⟩ := ih (ε / (2 * α)) (by positivity)
    have hm1 := (bs_tbi_spec hC k J hJ).1
    have hm2 := (bs_cp_spec hC π' k J hJ).1
    obtain ⟨μ0, hμ0⟩ := bs_tb_approx hC _ hm1 (ε / 2) (by positivity)
    have hd : ‖bs_cp hC π' k J - (bs_tb hC)^[k] J‖ ≤ ε / (2 * α) := by
      apply bs_norm_le _ _ _ (by positivity)
      intro x
      have := bs_tbi_le hC J hJ k π' x
      have := hπ' x
      rw [abs_le]; constructor <;> linarith
    let π : P.Policy := fun n => Nat.casesOn n μ0 (fun n => π' n)
    refine ⟨π, fun x => ?_⟩
    rw [bs_cp_succ', Function.iterate_succ_apply']
    show bs_tm hC μ0 (bs_cp hC π' k J) x ≤ _
    have hl := bs_tm_lip hC μ0 _ _ hm2 hm1
    have h3 := bs_abs_le_norm (bs_tm hC μ0 (bs_cp hC π' k J)) (bs_tm hC μ0 ((bs_tb hC)^[k] J)) x
    have h4 : α * ‖bs_cp hC π' k J - (bs_tb hC)^[k] J‖ ≤ α * (ε / (2 * α)) :=
      mul_le_mul_of_nonneg_left hd hα.le
    have h5 : α * (ε / (2 * α)) = ε / 2 := by field_simp
    have h6 := hμ0 x
    have h7 := (abs_le.1 h3).2
    linarith

lemma bs_tb_contr1 (hC : AssumptionC P Bbar m ρ α) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) (x : S) :
    (bs_tb hC)^[m] J x ≤ (bs_tb hC)^[m] J' x + ρ * ‖J - J'‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨π, hπ⟩ := bs_tbi_approx hC J' hJ' m ε hε
  have h1 := bs_tbi_le hC J hJ m π x
  have h2 := bs_cp_contr hC π J J' hJ hJ'
  have h3 := (abs_le.1 (bs_abs_le_norm (bs_cp hC π m J) (bs_cp hC π m J') x)).2
  have h4 := hπ x
  linarith

lemma bs_tb_contr (hC : AssumptionC P Bbar m ρ α) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) : ‖(bs_tb hC)^[m] J - (bs_tb hC)^[m] J'‖ ≤ ρ * ‖J - J'‖ := by
  apply bs_norm_le _ _ _ (mul_nonneg hC.ρ_pos.le (norm_nonneg _))
  intro x
  have h1 := bs_tb_contr1 hC J J' hJ hJ' x
  have h2 := bs_tb_contr1 hC J' J hJ' hJ x
  rw [norm_sub_rev J' J] at h2
  rw [abs_le]; constructor <;> linarith

lemma bs_tm_contr (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) : ‖(bs_tm hC μ)^[m] J - (bs_tm hC μ)^[m] J'‖ ≤ ρ * ‖J - J'‖ := by
  rw [← bs_cp_stat, ← bs_cp_stat]
  exact bs_cp_contr hC _ J J' hJ hJ'

lemma bs_Bbar_ne (hC : AssumptionC P Bbar m ρ α) : Bbar.Nonempty := by
  obtain ⟨J, hJ, -⟩ := hC.J0_mem; exact ⟨J, hJ⟩

lemma bs_T_fp (hC : AssumptionC P Bbar m ρ α) :
    ∃ Jf ∈ Bbar, bs_tb hC Jf = Jf ∧ (∀ J ∈ Bbar, bs_tb hC J = J → J = Jf) ∧
      (∀ J ∈ Bbar, Tendsto (fun N => (bs_tb hC)^[N] J) atTop (𝓝 Jf)) ∧
      (∀ J ∈ Bbar, ‖J - Jf‖ * (1 - ρ) ≤ ‖(bs_tb hC)^[m] J - J‖) :=
  bs_fp_gen Bbar hC.isClosed (bs_Bbar_ne hC) _ (fun J hJ => (bs_tb_spec hC J hJ).1) m hC.m_pos ρ
    hC.ρ_pos.le hC.ρ_lt_one (fun J hJ J' hJ' => bs_tb_contr hC J J' hJ hJ')

lemma bs_Tmu_fp (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) :
    ∃ Jf ∈ Bbar, bs_tm hC μ Jf = Jf ∧ (∀ J ∈ Bbar, bs_tm hC μ J = J → J = Jf) ∧
      (∀ J ∈ Bbar, Tendsto (fun N => (bs_tm hC μ)^[N] J) atTop (𝓝 Jf)) ∧
      (∀ J ∈ Bbar, ‖J - Jf‖ * (1 - ρ) ≤ ‖(bs_tm hC μ)^[m] J - J‖) :=
  bs_fp_gen Bbar hC.isClosed (bs_Bbar_ne hC) _ (fun J hJ => (bs_tm_spec hC μ J hJ).1) m hC.m_pos
    ρ hC.ρ_pos.le hC.ρ_lt_one (fun J hJ J' hJ' => bs_tm_contr hC μ J J' hJ hJ')

end ModelPart


section Main
variable {S C : Type*} {P : Model S C} {Bbar : Set (BFun S)} {m : ℕ} {ρ α : ℝ}

lemma bs_eval_tendsto {f : ℕ → BFun S} {g : BFun S} (h : Tendsto f atTop (𝓝 g)) (x : S) :
    Tendsto (fun N => f N x) atTop (𝓝 (g x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  apply squeeze_zero (fun N => norm_nonneg _) _ h
  intro N
  simpa [Real.norm_eq_abs] using bs_abs_le_norm (f N) g x

lemma bs_eval_tendsto' {f : ℕ → BFun S} {g : BFun S} (h : Tendsto f atTop (𝓝 g)) (x : S) :
    Tendsto (fun N => ((f N x : ℝ) : EReal)) atTop (𝓝 ((g x : ℝ) : EReal)) :=
  EReal.tendsto_coe.2 (bs_eval_tendsto h x)

noncomputable def bs_Jt (hC : AssumptionC P Bbar m ρ α) : BFun S := Classical.choose (bs_T_fp hC)

lemma bs_Jt_spec (hC : AssumptionC P Bbar m ρ α) :
    bs_Jt hC ∈ Bbar ∧ bs_tb hC (bs_Jt hC) = bs_Jt hC ∧
      (∀ J ∈ Bbar, bs_tb hC J = J → J = bs_Jt hC) ∧
      (∀ J ∈ Bbar, Tendsto (fun N => (bs_tb hC)^[N] J) atTop (𝓝 (bs_Jt hC))) ∧
      (∀ J ∈ Bbar, ‖J - bs_Jt hC‖ * (1 - ρ) ≤ ‖(bs_tb hC)^[m] J - J‖) :=
  Classical.choose_spec (bs_T_fp hC)

noncomputable def bs_Jm (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) : BFun S :=
  Classical.choose (bs_Tmu_fp hC μ)

lemma bs_Jm_spec (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) :
    bs_Jm hC μ ∈ Bbar ∧ bs_tm hC μ (bs_Jm hC μ) = bs_Jm hC μ ∧
      (∀ J ∈ Bbar, bs_tm hC μ J = J → J = bs_Jm hC μ) ∧
      (∀ J ∈ Bbar, Tendsto (fun N => (bs_tm hC μ)^[N] J) atTop (𝓝 (bs_Jm hC μ))) ∧
      (∀ J ∈ Bbar, ‖J - bs_Jm hC μ‖ * (1 - ρ) ≤ ‖(bs_tm hC μ)^[m] J - J‖) :=
  Classical.choose_spec (bs_Tmu_fp hC μ)

lemma bs_tmi_spec (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (k : ℕ) :
    ∀ J ∈ Bbar, (bs_tm hC μ)^[k] J ∈ Bbar ∧ toF ((bs_tm hC μ)^[k] J) = (P.Tmu μ)^[k] (toF J) := by
  induction k with
  | zero => intro J hJ; exact ⟨hJ, rfl⟩
  | succ k ih =>
    intro J hJ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := ih J hJ
    have h2 := bs_tm_spec hC μ _ h1.1
    exact ⟨h2.1, by rw [h2.2, h1.2]⟩

lemma bs_Jmu_eq (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) :
    P.Jmu μ = toF (bs_Jm hC μ) := by
  obtain ⟨J0', hJ0', hJ0eq⟩ := hC.J0_mem
  funext x
  have ht := bs_eval_tendsto' ((bs_Jm_spec hC μ).2.2.2.1 J0' hJ0') x
  have he : (fun N => P.comp (P.stationary μ) N P.J0 x) =
      fun N => ((((bs_tm hC μ)^[N] J0') x : ℝ) : EReal) := by
    funext N
    rw [hJ0eq, ← (bs_cp_spec hC _ N J0' hJ0').2, bs_cp_stat]
    rfl
  show limUnder atTop (fun N => P.comp (P.stationary μ) N P.J0 x) = _
  rw [he]
  exact ht.limUnder_eq

lemma bs_Jpi_ge (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (x : S) :
    ((bs_Jt hC x : ℝ) : EReal) ≤ P.Jpi π x := by
  obtain ⟨J0', hJ0', hJ0eq⟩ := hC.J0_mem
  obtain ⟨r, hr⟩ := hC.limit_real π x
  have hJ : P.Jpi π x = (r : EReal) := hr.limUnder_eq
  rw [hJ]
  refine le_of_tendsto_of_tendsto' (bs_eval_tendsto' ((bs_Jt_spec hC).2.2.2.1 J0' hJ0') x) hr ?_
  intro N
  show _ ≤ P.comp π N P.J0 x
  rw [hJ0eq, ← (bs_cp_spec hC π N J0' hJ0').2]
  exact EReal.coe_le_coe_iff.2 (bs_tbi_le hC J0' hJ0' N π x)

lemma bs_iter_dist (hC : AssumptionC P Bbar m ρ α) (μ : P.Selector) (J : BFun S) (hJ : J ∈ Bbar)
    (n : ℕ) : ‖(bs_tm hC μ)^[n] J - J‖ ≤ (∑ i ∈ Finset.range n, α ^ i) * ‖bs_tm hC μ J - J‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Finset.sum_range_succ, add_mul]
    have h1 := norm_sub_le_norm_sub_add_norm_sub ((bs_tm hC μ)^[n] (bs_tm hC μ J))
      ((bs_tm hC μ)^[n] J) J
    have h2 := bs_cp_lip hC (P.stationary μ) n _ (bs_tm_spec hC μ J hJ).1 J hJ
    rw [bs_cp_stat, bs_cp_stat] at h2
    linarith

lemma bs_near_opt (hC : AssumptionC P Bbar m ρ α) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : P.Selector, ‖bs_Jm hC μ - bs_Jt hC‖ ≤ ε := by
  obtain ⟨hJt, hfix, -, -, -⟩ := bs_Jt_spec hC
  set A := ∑ i ∈ Finset.range m, α ^ i with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => pow_nonneg hC.α_pos.le _
  have hρ : 0 < 1 - ρ := by linarith [hC.ρ_lt_one]
  set δ := ε * (1 - ρ) / (A + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨μ, hμ⟩ := bs_tb_approx hC _ hJt δ hδ0
  refine ⟨μ, ?_⟩
  have hd : ‖bs_tm hC μ (bs_Jt hC) - bs_Jt hC‖ ≤ δ := by
    apply bs_norm_le _ _ _ hδ0.le
    intro x
    have h1 := bs_tb_le hC μ _ hJt x
    have h2 := hμ x
    rw [hfix] at h1 h2
    rw [abs_le]; constructor <;> linarith
  have he := (bs_Jm_spec hC μ).2.2.2.2 _ hJt
  have hi := bs_iter_dist hC μ _ hJt m
  have h3 : A * δ ≤ ε * (1 - ρ) := by
    rw [hδ, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hε hρ]
  have h4 : ‖bs_Jt hC - bs_Jm hC μ‖ * (1 - ρ) ≤ ε * (1 - ρ) := by
    have := mul_le_mul_of_nonneg_left hd hA0
    linarith
  rw [norm_sub_rev]
  exact le_of_mul_le_mul_right h4 hρ

lemma bs_Jstar_eq (hC : AssumptionC P Bbar m ρ α) : P.Jstar = toF (bs_Jt hC) := by
  funext x
  apply le_antisymm
  · apply bs_ereal_le_of_eps
    intro ε hε
    obtain ⟨μ, hμ⟩ := bs_near_opt hC ε hε
    have h1 : P.Jstar x ≤ P.Jmu μ x := iInf_le (fun π => P.Jpi π x) (P.stationary μ)
    rw [bs_Jmu_eq hC μ] at h1
    refine h1.trans (EReal.coe_le_coe_iff.2 ?_)
    have := (abs_le.1 (bs_abs_le_norm (bs_Jm hC μ) (bs_Jt hC) x)).2
    linarith
  · exact le_iInf fun π => bs_Jpi_ge hC π x

theorem optimal_core {S C : Type*} (P : Model S C) (Bbar : Set (BFun S))
    (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    ((∃ Js ∈ Bbar, P.Jstar = toF Js) ∧
      P.T P.Jstar = P.Jstar ∧
      (∀ J ∈ Bbar, P.T (toF J) = toF J → toF J = P.Jstar) ∧
      (∀ J ∈ Bbar, P.T (toF J) ≤ toF J → P.Jstar ≤ toF J) ∧
      (∀ J ∈ Bbar, toF J ≤ P.T (toF J) → toF J ≤ P.Jstar)) ∧
    (∀ μ : P.Selector,
      (∃ Jm ∈ Bbar, P.Jmu μ = toF Jm) ∧
      P.Tmu μ (P.Jmu μ) = P.Jmu μ ∧
      (∀ J ∈ Bbar, P.Tmu μ (toF J) = toF J → toF J = P.Jmu μ)) ∧
    ((∀ J ∈ Bbar, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        SupDistLe (P.T^[N] (toF J)) P.Jstar ε) ∧
      (∀ μ : P.Selector, ∀ J ∈ Bbar, ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀,
        SupDistLe ((P.Tmu μ)^[N] (toF J)) (P.Jmu μ) ε)) := by
  obtain ⟨hJt, hfix, huniq, htend, -⟩ := bs_Jt_spec hC
  have hJs := bs_Jstar_eq hC
  refine ⟨⟨⟨_, hJt, hJs⟩, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hJs, ← (bs_tb_spec hC _ hJt).2, hfix]
  · intro J hJ h
    rw [← (bs_tb_spec hC J hJ).2] at h
    rw [hJs, huniq J hJ (bs_toF_injective h)]
  · intro J hJ h x
    have h1 : ∀ x, bs_tb hC J x ≤ J x := fun x => by
      have := h x
      rw [← (bs_tb_spec hC J hJ).2] at this
      exact EReal.coe_le_coe_iff.1 this
    have h2 : ∀ N, ∀ x, (bs_tb hC)^[N] J x ≤ J x := by
      intro N; induction N with
      | zero => intro x; exact le_rfl
      | succ N ih =>
        intro x
        rw [Function.iterate_succ_apply']
        exact (bs_tb_mono hC _ _ (bs_tbi_spec hC N J hJ).1 hJ ih x).trans (h1 x)
    rw [hJs]
    exact EReal.coe_le_coe_iff.2 (le_of_tendsto' (bs_eval_tendsto (htend J hJ) x) fun N => h2 N x)
  · intro J hJ h x
    have h1 : ∀ x, J x ≤ bs_tb hC J x := fun x => by
      have := h x
      rw [← (bs_tb_spec hC J hJ).2] at this
      exact EReal.coe_le_coe_iff.1 this
    have h2 : ∀ N, ∀ x, J x ≤ (bs_tb hC)^[N] J x := by
      intro N; induction N with
      | zero => intro x; exact le_rfl
      | succ N ih =>
        intro x
        rw [Function.iterate_succ_apply']
        exact (h1 x).trans (bs_tb_mono hC _ _ hJ (bs_tbi_spec hC N J hJ).1 ih x)
    rw [hJs]
    exact EReal.coe_le_coe_iff.2 (ge_of_tendsto' (bs_eval_tendsto (htend J hJ) x) fun N => h2 N x)
  · intro μ
    obtain ⟨hJm, hmfix, hmuniq, -, -⟩ := bs_Jm_spec hC μ
    have hJe := bs_Jmu_eq hC μ
    refine ⟨⟨_, hJm, hJe⟩, ?_, ?_⟩
    · rw [hJe, ← (bs_tm_spec hC μ _ hJm).2, hmfix]
    · intro J hJ h
      rw [← (bs_tm_spec hC μ J hJ).2] at h
      rw [hJe, hmuniq J hJ (bs_toF_injective h)]
  · intro J hJ ε hε
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (htend J hJ) ε hε
    refine ⟨N0, fun N hN => ?_⟩
    rw [← (bs_tbi_spec hC N J hJ).2, hJs, bs_supDist_iff]
    intro x
    have := hN0 N hN
    rw [dist_eq_norm] at this
    exact (bs_abs_le_norm _ _ x).trans this.le
  · intro μ J hJ ε hε
    obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 ((bs_Jm_spec hC μ).2.2.2.1 J hJ) ε hε
    refine ⟨N0, fun N hN => ?_⟩
    rw [← (bs_tmi_spec hC μ N J hJ).2, bs_Jmu_eq hC μ, bs_supDist_iff]
    intro x
    have := hN0 N hN
    rw [dist_eq_norm] at this
    exact (bs_abs_le_norm _ _ x).trans this.le

end Main


section More
variable {S C : Type*} {P : Model S C} {Bbar : Set (BFun S)} {m : ℕ} {ρ α : ℝ}

lemma bs_Jpi_ge_Tmu (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (x : S) :
    ((bs_tm hC (π 0) (bs_Jt hC) x : ℝ) : EReal) ≤ P.Jpi π x := by
  obtain ⟨J0', hJ0', hJ0eq⟩ := hC.J0_mem
  obtain ⟨hJt, -, -, htend, -⟩ := bs_Jt_spec hC
  obtain ⟨r, hr⟩ := hC.limit_real π x
  have hJ : P.Jpi π x = (r : EReal) := hr.limUnder_eq
  rw [hJ]
  have hr1 := hr.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun N => bs_tm hC (π 0) ((bs_tb hC)^[N] J0')) atTop
      (𝓝 (bs_tm hC (π 0) (bs_Jt hC))) := by
    have h0 := htend J0' hJ0'
    rw [tendsto_iff_norm_sub_tendsto_zero] at h0 ⊢
    apply squeeze_zero (fun N => norm_nonneg _)
      (fun N => bs_tm_lip hC (π 0) _ _ (bs_tbi_spec hC N J0' hJ0').1 hJt)
    simpa using h0.const_mul α
  refine le_of_tendsto_of_tendsto' (bs_eval_tendsto' ht x) hr1 ?_
  intro N
  show _ ≤ P.comp π (N + 1) P.J0 x
  rw [hJ0eq, ← (bs_cp_spec hC π (N + 1) J0' hJ0').2]
  show _ ≤ ((bs_cp hC π (N + 1) J0' x : ℝ) : EReal)
  rw [bs_cp_succ']
  apply EReal.coe_le_coe_iff.2
  exact bs_tm_mono hC _ _ _ (bs_tbi_spec hC N J0' hJ0').1
    (bs_cp_spec hC _ N J0' hJ0').1 (bs_tbi_le hC J0' hJ0' N _) x

theorem stationary_core {S C : Type*} (P : Model S C) (Bbar : Set (BFun S))
    (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    (∀ μs : P.Selector,
      (P.Jmu μs = P.Jstar ↔ P.Tmu μs P.Jstar = P.T P.Jstar) ∧
      (P.Jmu μs = P.Jstar ↔ P.Tmu μs (P.Jmu μs) = P.T (P.Jmu μs))) ∧
    ((∀ x : S, ∃ π : P.Policy, P.Jpi π x = P.Jstar x) →
      ∃ μs : P.Selector, P.Jmu μs = P.Jstar) ∧
    (∀ ε : ℝ, 0 < ε → ∃ με : P.Selector, SupDistLe P.Jstar (P.Jmu με) ε) := by
  obtain ⟨hJt, hfix, huniq, htend, -⟩ := bs_Jt_spec hC
  have hJs := bs_Jstar_eq hC
  refine ⟨?_, ?_, ?_⟩
  · intro μ
    obtain ⟨hJm, hmfix, hmuniq, -, -⟩ := bs_Jm_spec hC μ
    rw [bs_Jmu_eq hC μ, hJs, ← (bs_tm_spec hC μ _ hJt).2, ← (bs_tb_spec hC _ hJt).2, hfix,
      ← (bs_tm_spec hC μ _ hJm).2, ← (bs_tb_spec hC _ hJm).2, hmfix]
    constructor
    · constructor
      · intro h
        have h' := bs_toF_injective h
        rw [← h', hmfix]
      · intro h
        rw [hmuniq _ hJt (bs_toF_injective h)]
    · constructor
      · intro h
        have h' := bs_toF_injective h
        rw [h', hfix]
      · intro h
        rw [huniq _ hJm (bs_toF_injective h).symm]
  · intro h
    choose πx hπx using h
    let μs : P.Selector := ⟨fun x => (πx x 0).1 x, fun x => (πx x 0).2 x⟩
    refine ⟨μs, ?_⟩
    have hfx : bs_tm hC μs (bs_Jt hC) = bs_Jt hC := by
      apply lp.ext; funext x
      apply le_antisymm
      · have h1 := bs_Jpi_ge_Tmu hC (πx x) x
        rw [hπx x, hJs, bs_tm_apply hC _ _ hJt] at h1
        rw [← EReal.coe_le_coe_iff, bs_tm_apply hC _ _ hJt]
        exact h1
      · have := bs_tb_le hC μs _ hJt x
        rwa [hfix] at this
    obtain ⟨hJm, -, hmuniq, -, -⟩ := bs_Jm_spec hC μs
    rw [bs_Jmu_eq hC, hJs, ← hmuniq _ hJt hfx]
  · intro ε hε
    obtain ⟨μ, hμ⟩ := bs_near_opt hC ε hε
    refine ⟨μ, ?_⟩
    rw [hJs, bs_Jmu_eq hC μ, bs_supDist_iff]
    intro x
    rw [norm_sub_rev] at hμ
    exact (bs_abs_le_norm _ _ x).trans hμ

lemma bs_cp_contr_k (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (q : ℕ) :
    ∀ J ∈ Bbar, ∀ J' ∈ Bbar,
      ‖bs_cp hC π (m * q) J - bs_cp hC π (m * q) J'‖ ≤ ρ ^ q * ‖J - J'‖ := by
  induction q with
  | zero => intro J _ J' _; simp [bs_cp]
  | succ q ih =>
    intro J hJ J' hJ'
    rw [Nat.mul_succ, bs_cp_add, bs_cp_add]
    have h1 := ih _ (bs_cp_spec hC (fun n => π (m * q + n)) m J hJ).1 _
      (bs_cp_spec hC (fun n => π (m * q + n)) m J' hJ').1
    have h2 := bs_cp_contr hC (fun n => π (m * q + n)) J J' hJ hJ'
    calc _ ≤ _ := h1
      _ ≤ ρ ^ q * (ρ * ‖J - J'‖) := mul_le_mul_of_nonneg_left h2 (pow_nonneg hC.ρ_pos.le _)
      _ = _ := by ring

lemma bs_cp_diff (hC : AssumptionC P Bbar m ρ α) (π : P.Policy) (J J' : BFun S) (hJ : J ∈ Bbar)
    (hJ' : J' ∈ Bbar) :
    Tendsto (fun N => ‖bs_cp hC π N J - bs_cp hC π N J'‖) atTop (𝓝 0) := by
  have hm := hC.m_pos
  set K := (∑ r ∈ Finset.range m, α ^ r) * ‖J - J'‖ with hK
  have hb : ∀ N, ‖bs_cp hC π N J - bs_cp hC π N J'‖ ≤ ρ ^ (N / m) * K := by
    intro N
    have hN : N % m + m * (N / m) = N := Nat.mod_add_div N m
    conv_lhs => rw [← hN, bs_cp_add, bs_cp_add]
    have h1 := bs_cp_lip hC π (N % m) _
      (bs_cp_spec hC (fun n => π (N % m + n)) (m * (N / m)) J hJ).1 _
      (bs_cp_spec hC (fun n => π (N % m + n)) (m * (N / m)) J' hJ').1
    have h2 := bs_cp_contr_k hC (fun n => π (N % m + n)) (N / m) J hJ J' hJ'
    have h3 : α ^ (N % m) ≤ ∑ r ∈ Finset.range m, α ^ r :=
      Finset.single_le_sum (f := fun r => α ^ r) (fun r _ => pow_nonneg hC.α_pos.le r)
        (Finset.mem_range.2 (Nat.mod_lt N hm))
    have hρk := pow_nonneg hC.ρ_pos.le (N / m)
    have hn := norm_nonneg (J - J')
    calc _ ≤ α ^ (N % m) * _ := h1
      _ ≤ α ^ (N % m) * (ρ ^ (N / m) * ‖J - J'‖) :=
          mul_le_mul_of_nonneg_left h2 (pow_nonneg hC.α_pos.le _)
      _ ≤ (∑ r ∈ Finset.range m, α ^ r) * (ρ ^ (N / m) * ‖J - J'‖) :=
          mul_le_mul_of_nonneg_right h3 (mul_nonneg hρk hn)
      _ = ρ ^ (N / m) * K := by rw [hK]; ring
  apply squeeze_zero (fun N => norm_nonneg _) hb
  have h1 : Tendsto (fun N : ℕ => ρ ^ (N / m)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hC.ρ_pos.le hC.ρ_lt_one).comp
      (Nat.tendsto_div_const_atTop hm.ne')
  simpa using h1.mul_const K

theorem prelim_core {S C : Type*} (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ)
    (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α) :
    (∀ J ∈ Bbar, ∀ (π : P.Policy) (x : S),
      Tendsto (fun N => P.comp π N P.J0 x) atTop (𝓝 (P.Jpi π x)) ∧
      Tendsto (fun N => P.comp π N (toF J) x) atTop (𝓝 (P.Jpi π x))) ∧
    (∀ N : ℕ, 1 ≤ N → ∀ J ∈ Bbar,
      (fun x => ⨅ π : P.Policy, P.comp π N (toF J) x) = P.T^[N] (toF J)) ∧
    (∀ N : ℕ, 1 ≤ N → P.JNstar N = P.T^[N] P.J0) ∧
    (∀ J ∈ Bbar, ∀ J' ∈ Bbar,
      SupDistLe (P.T^[m] (toF J)) (P.T^[m] (toF J')) (ρ * ‖J - J'‖)) ∧
    (∀ μ : P.Selector, ∀ J ∈ Bbar, ∀ J' ∈ Bbar,
      SupDistLe ((P.Tmu μ)^[m] (toF J)) ((P.Tmu μ)^[m] (toF J')) (ρ * ‖J - J'‖)) := by
  obtain ⟨J0', hJ0', hJ0eq⟩ := hC.J0_mem
  have hinf : ∀ N : ℕ, ∀ J ∈ Bbar,
      (fun x => ⨅ π : P.Policy, P.comp π N (toF J) x) = P.T^[N] (toF J) := by
    intro N J hJ
    funext x
    rw [← (bs_tbi_spec hC N J hJ).2]
    apply le_antisymm
    · apply bs_ereal_le_of_eps
      intro ε hε
      obtain ⟨π, hπ⟩ := bs_tbi_approx hC J hJ N ε hε
      refine (iInf_le _ π).trans ?_
      rw [← (bs_cp_spec hC π N J hJ).2]
      exact EReal.coe_le_coe_iff.2 (hπ x)
    · refine le_iInf fun π => ?_
      rw [← (bs_cp_spec hC π N J hJ).2]
      exact EReal.coe_le_coe_iff.2 (bs_tbi_le hC J hJ N π x)
  refine ⟨?_, fun N _ J hJ => hinf N J hJ, ?_, ?_, ?_⟩
  · intro J hJ π x
    obtain ⟨r, hr⟩ := hC.limit_real π x
    have hJ' : P.Jpi π x = (r : EReal) := hr.limUnder_eq
    rw [hJ']
    refine ⟨hr, ?_⟩
    have he : (fun N => P.comp π N P.J0 x) = fun N => ((bs_cp hC π N J0' x : ℝ) : EReal) := by
      funext N; rw [hJ0eq, ← (bs_cp_spec hC π N J0' hJ0').2]; rfl
    rw [he] at hr
    have hr' := EReal.tendsto_coe.1 hr
    have he2 : (fun N => P.comp π N (toF J) x) = fun N => ((bs_cp hC π N J x : ℝ) : EReal) := by
      funext N; rw [← (bs_cp_spec hC π N J hJ).2]; rfl
    rw [he2]
    apply EReal.tendsto_coe.2
    have hd : Tendsto (fun N => bs_cp hC π N J x - bs_cp hC π N J0' x) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      apply squeeze_zero (fun N => norm_nonneg _) _ (bs_cp_diff hC π J J0' hJ hJ0')
      intro N
      simpa [Real.norm_eq_abs] using bs_abs_le_norm (bs_cp hC π N J) (bs_cp hC π N J0') x
    have := hr'.add hd
    simpa using this
  · intro N _
    show (fun x => ⨅ π : P.Policy, P.comp π N P.J0 x) = _
    rw [hJ0eq]
    exact hinf N J0' hJ0'
  · intro J hJ J' hJ'
    rw [← (bs_tbi_spec hC m J hJ).2, ← (bs_tbi_spec hC m J' hJ').2, bs_supDist_iff]
    intro x
    exact (bs_abs_le_norm _ _ x).trans (bs_tb_contr hC J J' hJ hJ')
  · intro μ J hJ J' hJ'
    rw [← (bs_tmi_spec hC μ m J hJ).2, ← (bs_tmi_spec hC μ m J' hJ').2, bs_supDist_iff]
    intro x
    exact (bs_abs_le_norm _ _ x).trans (bs_tm_contr hC μ J J' hJ hJ')

end More


section Compact
variable {S C : Type*} [TopologicalSpace C] [T2Space C] {P : Model S C} {Bbar : Set (BFun S)}
  {m : ℕ} {ρ α : ℝ}

omit [TopologicalSpace C] [T2Space C] in
lemma bs_ev_level (hC : AssumptionC P Bbar m ρ α) (Jb : BFun S) (hJb : Jb ∈ Bbar) (kb : ℕ)
    (πs : P.Policy)
    (h6 : ∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb))
    (x : S) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in atTop, (πs k).1 x ∈ {u : C | u ∈ P.U x ∧ P.H x u (P.T^[j] (toF Jb)) ≤
      ((bs_Jt hC x + ε + α * (‖(bs_tb hC)^[j] Jb - bs_Jt hC‖ + ε) : ℝ) : EReal)} := by
  obtain ⟨hJt, -, -, htend, -⟩ := bs_Jt_spec hC
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (htend Jb hJb) ε hε
  rw [eventually_atTop]
  refine ⟨max N0 kb, fun k hk => ⟨(πs k).2 x, ?_⟩⟩
  have hk1 : N0 ≤ k := le_of_max_le_left hk
  have hk2 : kb ≤ k := le_of_max_le_right hk
  set G : ℕ → BFun S := fun n => (bs_tb hC)^[n] Jb with hG
  have hGm : ∀ n, G n ∈ Bbar := fun n => (bs_tbi_spec hC n Jb hJb).1
  have h6' : bs_tm hC (πs k) (G k) = G (k + 1) := by
    apply bs_toF_injective
    rw [(bs_tm_spec hC _ _ (hGm k)).2, (bs_tbi_spec hC k Jb hJb).2,
      (bs_tbi_spec hC (k + 1) Jb hJb).2]
    exact h6 k hk2
  rw [← (bs_tbi_spec hC j Jb hJb).2]
  rw [← bs_tm_apply hC (πs k) _ (hGm j) x]
  apply EReal.coe_le_coe_iff.2
  have l1 := (abs_le.1 ((bs_abs_le_norm _ _ x).trans
    (bs_tm_lip hC (πs k) (G j) (G k) (hGm j) (hGm k)))).2
  rw [h6'] at l1
  have l2 : ‖G j - G k‖ ≤ ‖G j - bs_Jt hC‖ + ‖G k - bs_Jt hC‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub (G j) (bs_Jt hC) (G k)
    rwa [norm_sub_rev (bs_Jt hC) (G k)] at this
  have l3 : ‖G k - bs_Jt hC‖ < ε := by
    have := hN0 k hk1; rwa [dist_eq_norm] at this
  have l4 : ‖G (k + 1) - bs_Jt hC‖ < ε := by
    have := hN0 (k + 1) (by omega); rwa [dist_eq_norm] at this
  have l5 := (abs_le.1 (bs_abs_le_norm (G (k + 1)) (bs_Jt hC) x)).2
  have hα := hC.α_pos
  have l6 : α * ‖G j - G k‖ ≤ α * (‖G j - bs_Jt hC‖ + ε) := by
    apply mul_le_mul_of_nonneg_left _ hα.le; linarith
  show bs_tm hC (πs k) (G j) x ≤ _
  linarith

theorem compact_core (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ) (ρ α : ℝ)
    (hC : AssumptionC P Bbar m ρ α)
    (Jb : BFun S) (hJb : Jb ∈ Bbar) (kb : ℕ) (hkb : 0 < kb)
    (hcompact : ∀ (x : S) (lam : ℝ), ∀ k ≥ kb,
      IsCompact {u : C | u ∈ P.U x ∧ P.H x u (P.T^[k] (toF Jb)) ≤ (lam : EReal)}) :
    (∃ πs : P.Policy, ∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) ∧
    (∃ μs : P.Selector, P.Jmu μs = P.Jstar) ∧
    (∀ πs : P.Policy, (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ x : S, ∃ u : C, MapClusterPt u atTop (fun k : ℕ => (πs k).1 x)) ∧
    (∀ πs : P.Policy, (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ μs : S → C, (∀ x : S, MapClusterPt (μs x) atTop (fun k : ℕ => (πs k).1 x)) →
        ∃ hμs : ∀ x, μs x ∈ P.U x, P.Jmu ⟨μs, hμs⟩ = P.Jstar) := by
  obtain ⟨hJt, hfix, huniq, htend, -⟩ := bs_Jt_spec hC
  have hJs := bs_Jstar_eq hC
  have hα := hC.α_pos
  set G : ℕ → BFun S := fun n => (bs_tb hC)^[n] Jb with hG
  have hGm : ∀ n, G n ∈ Bbar := fun n => (bs_tbi_spec hC n Jb hJb).1
  -- (a)
  have partA : ∃ πs : P.Policy, ∀ k ≥ kb,
      P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb) := by
    have key : ∀ k, ∀ x, ∃ u ∈ P.U x, kb ≤ k →
        P.H x u (P.T^[k] (toF Jb)) ≤ P.T (P.T^[k] (toF Jb)) x := by
      intro k x
      by_cases hk : kb ≤ k
      · set t : ℝ := G (k + 1) x with ht
        have htv : P.T (P.T^[k] (toF Jb)) x = (t : EReal) := by
          rw [← Function.iterate_succ_apply' P.T k, ← (bs_tbi_spec hC (k + 1) Jb hJb).2]
          rfl
        let K : ℕ → Set C := fun n => {u : C | u ∈ P.U x ∧
          P.H x u (P.T^[k] (toF Jb)) ≤ ((t + 1 / ((n : ℝ) + 1) : ℝ) : EReal)}
        have hKc : ∀ n, IsCompact (K n) := fun n => hcompact x _ k hk
        have hne : (⋂ n, K n).Nonempty := by
          apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K
          · intro n u hu
            refine ⟨hu.1, hu.2.trans (EReal.coe_le_coe_iff.2 ?_)⟩
            have : 1 / ((n + 1 : ℕ) : ℝ) + 1 ≥ 1 / ((n : ℝ) + 1) := by
              push_cast
              apply le_add_of_le_of_nonneg _ zero_le_one
              apply one_div_le_one_div_of_le (by positivity); linarith
            push_cast at this ⊢
            have h2 : 1 / ((n : ℝ) + 1 + 1) ≤ 1 / ((n : ℝ) + 1) :=
              one_div_le_one_div_of_le (by positivity) (by linarith)
            linarith
          · intro n
            have hlt : P.T (P.T^[k] (toF Jb)) x < ((t + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
              rw [htv]; exact EReal.coe_lt_coe_iff.2 (by have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
                                                         linarith)
            obtain ⟨u, hu⟩ := iInf_lt_iff.1 hlt
            obtain ⟨hu', hu''⟩ := iInf_lt_iff.1 hu
            exact ⟨u, hu', hu''.le⟩
          · exact hKc 0
          · intro n; exact (hKc n).isClosed
        obtain ⟨u, hu⟩ := hne
        rw [Set.mem_iInter] at hu
        refine ⟨u, (hu 0).1, fun _ => ?_⟩
        rw [htv]
        apply bs_ereal_le_of_eps
        intro ε hε
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        exact (hu n).2.trans (EReal.coe_le_coe_iff.2 (by linarith))
      · exact ⟨(P.U_nonempty x).some, (P.U_nonempty x).some_mem, fun h => absurd h hk⟩
    choose u hu hle using key
    refine ⟨fun k => ⟨u k, hu k⟩, fun k hk => ?_⟩
    funext x
    rw [Function.iterate_succ_apply']
    apply le_antisymm (hle k x hk)
    exact iInf₂_le (u k x) (hu k x)
  -- (c)
  have partC : ∀ πs : P.Policy,
      (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ x : S, ∃ u : C, MapClusterPt u atTop (fun k : ℕ => (πs k).1 x) := by
    intro πs h6 x
    have hev := bs_ev_level hC Jb hJb kb πs h6 x kb 1 one_pos
    obtain ⟨u, -, hu⟩ := (hcompact x _ kb le_rfl).exists_mapClusterPt_of_frequently hev.frequently
    exact ⟨u, hu⟩
  -- (d)
  have partD : ∀ πs : P.Policy,
      (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ μs : S → C, (∀ x : S, MapClusterPt (μs x) atTop (fun k : ℕ => (πs k).1 x)) →
        ∃ hμs : ∀ x, μs x ∈ P.U x, P.Jmu ⟨μs, hμs⟩ = P.Jstar := by
    intro πs h6 μs hμ
    have hin : ∀ x, ∀ j ≥ kb, ∀ ε : ℝ, 0 < ε → μs x ∈ {u : C | u ∈ P.U x ∧
        P.H x u (P.T^[j] (toF Jb)) ≤
          ((bs_Jt hC x + ε + α * (‖(bs_tb hC)^[j] Jb - bs_Jt hC‖ + ε) : ℝ) : EReal)} := by
      intro x j hj ε hε
      have hev := bs_ev_level hC Jb hJb kb πs h6 x j ε hε
      have hcl := (hcompact x (bs_Jt hC x + ε + α * (‖(bs_tb hC)^[j] Jb - bs_Jt hC‖ + ε)) j hj).isClosed
      rw [← hcl.closure_eq, mem_closure_iff_clusterPt]
      exact ClusterPt.mono (f := Filter.map (fun k => (πs k).1 x) atTop) (hμ x) (tendsto_principal.2 hev)
    have hU : ∀ x, μs x ∈ P.U x := fun x => (hin x kb le_rfl 1 one_pos).1
    refine ⟨hU, ?_⟩
    set μ' : P.Selector := ⟨μs, hU⟩
    have hle : ∀ x, bs_tm hC μ' (bs_Jt hC) x ≤ bs_Jt hC x := by
      intro x
      apply le_of_forall_pos_le_add
      intro δ hδ
      have hev := Metric.tendsto_atTop.1 (htend Jb hJb) (δ / (4 * α)) (by positivity)
      obtain ⟨N0, hN0⟩ := hev
      set j := max N0 kb with hj
      have hj1 : ‖G j - bs_Jt hC‖ < δ / (4 * α) := by
        have := hN0 j (le_max_left _ _); rwa [dist_eq_norm] at this
      set ε := δ / (4 * (1 + α)) with hεdef
      have hε : 0 < ε := by positivity
      have h1 := (hin x j (le_max_right _ _) ε hε).2
      rw [← (bs_tbi_spec hC j Jb hJb).2, ← bs_tm_apply hC μ' _ (hGm j) x] at h1
      have h1' := EReal.coe_le_coe_iff.1 h1
      have h2 := (abs_le.1 ((bs_abs_le_norm _ _ x).trans
        (bs_tm_lip hC μ' (bs_Jt hC) (G j) hJt (hGm j)))).2
      rw [norm_sub_rev] at h2
      have e1 : α * (δ / (4 * α)) = δ / 4 := by field_simp
      have e2 : ε * (1 + α) = δ / 4 := by rw [hεdef]; field_simp
      have h3 : α * ‖G j - bs_Jt hC‖ ≤ δ / 4 := by
        rw [← e1]; exact mul_le_mul_of_nonneg_left hj1.le hα.le
      show bs_tm hC μ' (bs_Jt hC) x ≤ bs_Jt hC x + δ
      have h1'' : bs_tm hC μ' (G j) x ≤ bs_Jt hC x + ε + α * (‖G j - bs_Jt hC‖ + ε) := h1'
      nlinarith
    have hfx : bs_tm hC μ' (bs_Jt hC) = bs_Jt hC := by
      apply lp.ext; funext x
      apply le_antisymm (hle x)
      have := bs_tb_le hC μ' _ hJt x
      rwa [hfix] at this
    obtain ⟨hJm, -, hmuniq, -, -⟩ := bs_Jm_spec hC μ'
    rw [bs_Jmu_eq hC, hJs, ← hmuniq _ hJt hfx]
  refine ⟨partA, ?_, partC, partD⟩
  obtain ⟨πs, h6⟩ := partA
  choose μs hμs using partC πs h6
  obtain ⟨hU, hopt⟩ := partD πs h6 μs hμs
  exact ⟨_, hopt⟩

end Compact

end BertsekasShreve.Contraction

open BertsekasShreve.Contraction


theorem solution {S C : Type*} [TopologicalSpace C] [T2Space C]
    (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ) (ρ α : ℝ) (hC : AssumptionC P Bbar m ρ α)
    (Jb : BFun S) (hJb : Jb ∈ Bbar) (kb : ℕ) (hkb : 0 < kb)
    (hcompact : ∀ (x : S) (lam : ℝ), ∀ k ≥ kb,
      IsCompact {u : C | u ∈ P.U x ∧ P.H x u (P.T^[k] (toF Jb)) ≤ (lam : EReal)}) :
    (∃ πs : P.Policy, ∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) ∧
    (∃ μs : P.Selector, P.Jmu μs = P.Jstar) ∧
    (∀ πs : P.Policy, (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ x : S, ∃ u : C, MapClusterPt u atTop (fun k : ℕ => (πs k).1 x)) ∧
    (∀ πs : P.Policy, (∀ k ≥ kb, P.Tmu (πs k) (P.T^[k] (toF Jb)) = P.T^[k + 1] (toF Jb)) →
      ∀ μs : S → C, (∀ x : S, MapClusterPt (μs x) atTop (fun k : ℕ => (πs k).1 x)) →
        ∃ hμs : ∀ x, μs x ∈ P.U x, P.Jmu ⟨μs, hμs⟩ = P.Jstar) := by
  exact compact_core P Bbar m ρ α hC Jb hJb kb hkb hcompact
