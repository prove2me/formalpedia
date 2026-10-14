-- Prove2me | solution 1 for BertsekasShreve.Generalized.prop6_4_contraction_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:57:41.363079+00:00
-- url     : https://prove2.me/submissions/e85057f1-41e0-4bf8-ae77-8d115044e950

import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality



namespace BertsekasShreve.Generalized

open Filter Topology
open BertsekasShreve.Contraction (BFun toF SupDistLe)

namespace G64

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

section GenEReal
variable {S C : Type*} (P : Model S C)

lemma g_comp_succ (π : P.Policy) (n : ℕ) (J : S → EReal) :
    P.comp π (n + 1) J = P.Tmu (π 0).1 (P.comp (P.shift π 1) n J) := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    show P.comp π (n + 1) (P.Tmu (π (n + 1)).1 J) = _
    rw [ih]
    show _ = P.Tmu (π 0).1 (P.comp (P.shift π 1) n (P.Tmu (P.shift π 1 n).1 J))
    simp only [Model.shift, Nat.add_comm 1 n]

lemma g_comp_mem (hA3 : P.A3) (π : P.Policy) (n : ℕ) (J : S → EReal) (hJ : J ∈ P.Ftil) :
    P.comp π n J ∈ P.Ftil := by
  induction n generalizing π with
  | zero => exact hJ
  | succ n ih =>
    rw [g_comp_succ]
    exact ((hA3 _ (ih _)).1 _ (π 0).2)

lemma g_iterT_mem (hA2 : P.A2) (n : ℕ) (J : S → EReal) (hJ : J ∈ P.Fstar) :
    P.T^[n] J ∈ P.Fstar := by
  induction n with
  | zero => exact hJ
  | succ n ih => rw [Function.iterate_succ_apply']; exact (hA2 _ ih).1

lemma g_T_le_Tmu (μ : P.Sel) (J : S → EReal) : P.T J ≤ P.Tmu μ.1 J :=
  fun x => biInf_le (fun u => P.H x u J) (P.Mtil_subset _ μ.2 x)

lemma g_T_mono {J J' : S → EReal} (hJ : J ∈ P.Ftil) (hJ' : J' ∈ P.Ftil) (h : J ≤ J') :
    P.T J ≤ P.T J' := by
  intro x
  exact iInf₂_mono fun u hu => P.mono x u hu J hJ J' hJ' h

lemma g_iterT_le_comp (hA2 : P.A2) (hA3 : P.A3) (π : P.Policy) (n : ℕ) (J : S → EReal)
    (hJ : J ∈ P.Fstar) : P.T^[n] J ≤ P.comp π n J := by
  induction n generalizing π with
  | zero => exact le_rfl
  | succ n ih =>
    rw [g_comp_succ, Function.iterate_succ_apply']
    exact (g_T_mono P (P.Fstar_subset (g_iterT_mem P hA2 n J hJ)) (g_comp_mem P hA3 _ _ _
      (P.Fstar_subset hJ)) (ih _)).trans (g_T_le_Tmu P _ _)

end GenEReal

section ModelPart
variable {S C : Type*} {P : Model S C} {Bbar : Set (BFun S)} {m : ℕ} {ρ α : ℝ}

/-- `B̄ ∩ F̃` inside `B` -/
def gD (P : Model S C) (Bbar : Set (BFun S)) : Set (BFun S) := {J | J ∈ Bbar ∧ toF J ∈ P.Ftil}
/-- `B̄ ∩ F*` inside `B` -/
def gDs (P : Model S C) (Bbar : Set (BFun S)) : Set (BFun S) := {J | J ∈ Bbar ∧ toF J ∈ P.Fstar}

lemma gDs_sub {J : BFun S} (h : J ∈ gDs P Bbar) : J ∈ gD P Bbar := ⟨h.1, P.Fstar_subset h.2⟩

open Classical in
noncomputable def bs_tm (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J : BFun S) : BFun S :=
  if h : J ∈ gD P Bbar then Classical.choose (hC.Tmu_mem μ.1 μ.2 (toF J) ⟨J, h.1, rfl, h.2⟩) else J

lemma bs_tm_spec (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J : BFun S) (hJ : J ∈ gD P Bbar) :
    bs_tm hC μ J ∈ gD P Bbar ∧ toF (bs_tm hC μ J) = P.Tmu μ.1 (toF J) := by
  unfold bs_tm; rw [dif_pos hJ]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (hC.Tmu_mem μ.1 μ.2 (toF J) ⟨J, hJ.1, rfl, hJ.2⟩)
  exact ⟨⟨h1, h2 ▸ h3⟩, h2.symm⟩

open Classical in
noncomputable def bs_tb (hC : P.AssumptionCtilde Bbar m ρ α) (J : BFun S) : BFun S :=
  if h : J ∈ gDs P Bbar then Classical.choose (hC.T_mem (toF J) ⟨J, h.1, rfl, h.2⟩) else J

lemma bs_tb_spec (hC : P.AssumptionCtilde Bbar m ρ α) (J : BFun S) (hJ : J ∈ gDs P Bbar) :
    bs_tb hC J ∈ gDs P Bbar ∧ toF (bs_tb hC J) = P.T (toF J) := by
  unfold bs_tb; rw [dif_pos hJ]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec (hC.T_mem (toF J) ⟨J, hJ.1, rfl, hJ.2⟩)
  exact ⟨⟨h1, h2 ▸ h3⟩, h2.symm⟩

lemma bs_tm_apply (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J : BFun S) (hJ : J ∈ gD P Bbar)
    (x : S) : ((bs_tm hC μ J x : ℝ) : EReal) = P.H x (μ.1 x) (toF J) :=
  congrFun (bs_tm_spec hC μ J hJ).2 x

lemma bs_tb_apply (hC : P.AssumptionCtilde Bbar m ρ α) (J : BFun S) (hJ : J ∈ gDs P Bbar)
    (x : S) : ((bs_tb hC J x : ℝ) : EReal) = ⨅ u ∈ P.U x, P.H x u (toF J) :=
  congrFun (bs_tb_spec hC J hJ).2 x

lemma bs_tm_lip (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J J' : BFun S) (hJ : J ∈ gD P Bbar)
    (hJ' : J' ∈ gD P Bbar) : ‖bs_tm hC μ J - bs_tm hC μ J'‖ ≤ α * ‖J - J'‖ := by
  have h := hC.lipschitz μ.1 μ.2 J J' hJ.2 hJ'.2
  rw [← (bs_tm_spec hC μ J hJ).2, ← (bs_tm_spec hC μ J' hJ').2, bs_supDist_iff] at h
  exact bs_norm_le _ _ _ (mul_nonneg hC.α_pos.le (norm_nonneg _)) h

lemma bs_tm_mono (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J J' : BFun S) (hJ : J ∈ gD P Bbar)
    (hJ' : J' ∈ gD P Bbar) (h : ∀ x, J x ≤ J' x) (x : S) : bs_tm hC μ J x ≤ bs_tm hC μ J' x := by
  have := P.mono x (μ.1 x) (P.Mtil_subset _ μ.2 x) (toF J) hJ.2 (toF J') hJ'.2
    (fun y => EReal.coe_le_coe_iff.2 (h y))
  rw [← bs_tm_apply hC μ J hJ, ← bs_tm_apply hC μ J' hJ'] at this
  exact EReal.coe_le_coe_iff.1 this

lemma bs_tb_le (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J : BFun S) (hJ : J ∈ gDs P Bbar)
    (x : S) : bs_tb hC J x ≤ bs_tm hC μ J x := by
  have : (⨅ u ∈ P.U x, P.H x u (toF J)) ≤ P.H x (μ.1 x) (toF J) :=
    iInf₂_le (μ.1 x) (P.Mtil_subset _ μ.2 x)
  rw [← bs_tm_apply hC μ J (gDs_sub hJ), ← bs_tb_apply hC J hJ] at this
  exact EReal.coe_le_coe_iff.1 this

lemma bs_tb_mono (hC : P.AssumptionCtilde Bbar m ρ α) (J J' : BFun S) (hJ : J ∈ gDs P Bbar)
    (hJ' : J' ∈ gDs P Bbar) (h : ∀ x, J x ≤ J' x) (x : S) : bs_tb hC J x ≤ bs_tb hC J' x := by
  have : (⨅ u ∈ P.U x, P.H x u (toF J)) ≤ (⨅ u ∈ P.U x, P.H x u (toF J')) :=
    iInf₂_mono fun u hu => P.mono x u hu (toF J) (gDs_sub hJ).2 (toF J') (gDs_sub hJ').2
      (fun y => EReal.coe_le_coe_iff.2 (h y))
  rw [← bs_tb_apply hC J hJ, ← bs_tb_apply hC J' hJ'] at this
  exact EReal.coe_le_coe_iff.1 this

lemma bs_tb_approx (hA4 : P.A4) (hC : P.AssumptionCtilde Bbar m ρ α) (J : BFun S)
    (hJ : J ∈ gDs P Bbar) (ε : ℝ)
    (hε : 0 < ε) : ∃ μ : P.Sel, ∀ x, bs_tm hC μ J x ≤ bs_tb hC J x + ε := by
  obtain ⟨μ, hμ, h⟩ := hA4 (toF J) hJ.2 ε hε
  refine ⟨⟨μ, hμ⟩, fun x => ?_⟩
  have e1 := congrFun (bs_tb_spec hC J hJ).2 x
  have e2 := congrFun (bs_tm_spec hC ⟨μ, hμ⟩ J (gDs_sub hJ)).2 x
  have h1 := (h x).1 (by rw [← e1]; exact EReal.bot_lt_coe _)
  rw [← e1] at h1
  have h2 : P.Tmu μ (toF J) x = P.Tmu (⟨μ, hμ⟩ : P.Sel).1 (toF J) x := rfl
  rw [h2, ← e2] at h1
  simp only [toF] at h1
  rw [← EReal.coe_add] at h1
  exact EReal.coe_le_coe_iff.1 h1

noncomputable def bs_cp (hC : P.AssumptionCtilde Bbar m ρ α) (π : P.Policy) : ℕ → BFun S → BFun S
  | 0, J => J
  | N + 1, J => bs_cp hC π N (bs_tm hC (π N) J)

lemma bs_cp_spec (hC : P.AssumptionCtilde Bbar m ρ α) (π : P.Policy) (N : ℕ) :
    ∀ J ∈ gD P Bbar, bs_cp hC π N J ∈ gD P Bbar ∧ toF (bs_cp hC π N J) = P.comp π N (toF J) := by
  induction N with
  | zero => intro J hJ; exact ⟨hJ, rfl⟩
  | succ N ih =>
    intro J hJ
    have h1 := bs_tm_spec hC (π N) J hJ
    have h2 := ih _ h1.1
    refine ⟨h2.1, ?_⟩
    show toF (bs_cp hC π N (bs_tm hC (π N) J)) = P.comp π N (P.Tmu (π N).1 (toF J))
    rw [h2.2, h1.2]

lemma bs_cp_add (hC : P.AssumptionCtilde Bbar m ρ α) (π : P.Policy) (a b : ℕ) :
    ∀ J, bs_cp hC π (a + b) J = bs_cp hC π a (bs_cp hC (fun n => π (a + n)) b J) := by
  induction b with
  | zero => intro J; rfl
  | succ b ih =>
    intro J
    show bs_cp hC π (a + b) (bs_tm hC (π (a + b)) J) =
      bs_cp hC π a (bs_cp hC (fun n => π (a + n)) (b + 1) J)
    rw [ih]; rfl

lemma bs_cp_succ' (hC : P.AssumptionCtilde Bbar m ρ α) (π : P.Policy) (k : ℕ) (J : BFun S) :
    bs_cp hC π (k + 1) J = bs_tm hC (π 0) (bs_cp hC (fun n => π (n + 1)) k J) := by
  rw [show k + 1 = 1 + k from add_comm _ _, bs_cp_add]
  show bs_tm hC (π 0) _ = _
  congr 2
  funext n; rw [add_comm]

lemma bs_cp_lip (hC : P.AssumptionCtilde Bbar m ρ α) (π : P.Policy) (k : ℕ) :
    ∀ J ∈ gD P Bbar, ∀ J' ∈ gD P Bbar, ‖bs_cp hC π k J - bs_cp hC π k J'‖ ≤ α ^ k * ‖J - J'‖ := by
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

lemma bs_cp_contr (hC : P.AssumptionCtilde Bbar m ρ α) (π : P.Policy) (J J' : BFun S)
    (hJ : J ∈ gD P Bbar) (hJ' : J' ∈ gD P Bbar) :
    ‖bs_cp hC π m J - bs_cp hC π m J'‖ ≤ ρ * ‖J - J'‖ := by
  have h := hC.contraction π J hJ.1 J' hJ'.1 hJ.2 hJ'.2
  rw [← (bs_cp_spec hC π m J hJ).2, ← (bs_cp_spec hC π m J' hJ').2, bs_supDist_iff] at h
  exact bs_norm_le _ _ _ (mul_nonneg hC.ρ_pos.le (norm_nonneg _)) h

lemma bs_cp_stat (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (N : ℕ) :
    ∀ J, bs_cp hC (P.stationary μ) N J = (bs_tm hC μ)^[N] J := by
  induction N with
  | zero => intro J; rfl
  | succ N ih =>
    intro J
    show bs_cp hC (P.stationary μ) N (bs_tm hC μ J) = _
    rw [ih, Function.iterate_succ_apply]

lemma bs_default_policy (hA4 : P.A4) : Nonempty P.Policy := by
  obtain ⟨μ, hμ, -⟩ := hA4 P.J0 P.J0_mem 1 one_pos
  exact ⟨fun _ => ⟨μ, hμ⟩⟩

lemma bs_tbi_spec (hC : P.AssumptionCtilde Bbar m ρ α) (k : ℕ) :
    ∀ J ∈ gDs P Bbar, (bs_tb hC)^[k] J ∈ gDs P Bbar ∧
      toF ((bs_tb hC)^[k] J) = P.T^[k] (toF J) := by
  induction k with
  | zero => intro J hJ; exact ⟨hJ, rfl⟩
  | succ k ih =>
    intro J hJ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := ih J hJ
    have h2 := bs_tb_spec hC _ h1.1
    exact ⟨h2.1, by rw [h2.2, h1.2]⟩

lemma bs_tbi_le (hA2 : P.A2) (hA3 : P.A3) (hC : P.AssumptionCtilde Bbar m ρ α) (J : BFun S)
    (hJ : J ∈ gDs P Bbar) (k : ℕ) :
    ∀ (π : P.Policy) x, (bs_tb hC)^[k] J x ≤ bs_cp hC π k J x := by
  intro π x
  have h := g_iterT_le_comp P hA2 hA3 π k (toF J) hJ.2 x
  rw [← (bs_tbi_spec hC k J hJ).2, ← (bs_cp_spec hC π k J (gDs_sub hJ)).2] at h
  exact EReal.coe_le_coe_iff.1 h

lemma bs_tbi_approx (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hC : P.AssumptionCtilde Bbar m ρ α)
    (J : BFun S) (hJ : J ∈ gDs P Bbar) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ π : P.Policy, ∀ x, bs_cp hC π k J x ≤ (bs_tb hC)^[k] J x + ε := by
  induction k with
  | zero =>
    intro ε hε
    obtain ⟨π⟩ := bs_default_policy hA4
    exact ⟨π, fun x => by show J x ≤ J x + ε; linarith⟩
  | succ k ih =>
    intro ε hε
    have hα := hC.α_pos
    obtain ⟨π', hπ'⟩ := ih (ε / (2 * α)) (by positivity)
    have hm1 := (bs_tbi_spec hC k J hJ).1
    have hm2 := (bs_cp_spec hC π' k J (gDs_sub hJ)).1
    obtain ⟨μ0, hμ0⟩ := bs_tb_approx hA4 hC _ hm1 (ε / 2) (by positivity)
    have hd : ‖bs_cp hC π' k J - (bs_tb hC)^[k] J‖ ≤ ε / (2 * α) := by
      apply bs_norm_le _ _ _ (by positivity)
      intro x
      have := bs_tbi_le hA2 hA3 hC J hJ k π' x
      have := hπ' x
      rw [abs_le]; constructor <;> linarith
    let π : P.Policy := fun n => Nat.casesOn n μ0 (fun n => π' n)
    refine ⟨π, fun x => ?_⟩
    rw [bs_cp_succ', Function.iterate_succ_apply']
    show bs_tm hC μ0 (bs_cp hC π' k J) x ≤ _
    have hl := bs_tm_lip hC μ0 _ _ hm2 (gDs_sub hm1)
    have h3 := bs_abs_le_norm (bs_tm hC μ0 (bs_cp hC π' k J)) (bs_tm hC μ0 ((bs_tb hC)^[k] J)) x
    have h4 : α * ‖bs_cp hC π' k J - (bs_tb hC)^[k] J‖ ≤ α * (ε / (2 * α)) :=
      mul_le_mul_of_nonneg_left hd hα.le
    have h5 : α * (ε / (2 * α)) = ε / 2 := by field_simp
    have h6 := hμ0 x
    have h7 := (abs_le.1 h3).2
    linarith

lemma bs_tb_contr1 (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hC : P.AssumptionCtilde Bbar m ρ α)
    (J J' : BFun S) (hJ : J ∈ gDs P Bbar)
    (hJ' : J' ∈ gDs P Bbar) (x : S) :
    (bs_tb hC)^[m] J x ≤ (bs_tb hC)^[m] J' x + ρ * ‖J - J'‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨π, hπ⟩ := bs_tbi_approx hA2 hA3 hA4 hC J' hJ' m ε hε
  have h1 := bs_tbi_le hA2 hA3 hC J hJ m π x
  have h2 := bs_cp_contr hC π J J' (gDs_sub hJ) (gDs_sub hJ')
  have h3 := (abs_le.1 (bs_abs_le_norm (bs_cp hC π m J) (bs_cp hC π m J') x)).2
  have h4 := hπ x
  linarith

lemma bs_tb_contr (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hC : P.AssumptionCtilde Bbar m ρ α)
    (J J' : BFun S) (hJ : J ∈ gDs P Bbar)
    (hJ' : J' ∈ gDs P Bbar) : ‖(bs_tb hC)^[m] J - (bs_tb hC)^[m] J'‖ ≤ ρ * ‖J - J'‖ := by
  apply bs_norm_le _ _ _ (mul_nonneg hC.ρ_pos.le (norm_nonneg _))
  intro x
  have h1 := bs_tb_contr1 hA2 hA3 hA4 hC J J' hJ hJ' x
  have h2 := bs_tb_contr1 hA2 hA3 hA4 hC J' J hJ' hJ x
  rw [norm_sub_rev J' J] at h2
  rw [abs_le]; constructor <;> linarith

lemma bs_tm_contr (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J J' : BFun S)
    (hJ : J ∈ gD P Bbar)
    (hJ' : J' ∈ gD P Bbar) : ‖(bs_tm hC μ)^[m] J - (bs_tm hC μ)^[m] J'‖ ≤ ρ * ‖J - J'‖ := by
  rw [← bs_cp_stat, ← bs_cp_stat]
  exact bs_cp_contr hC _ J J' hJ hJ'

lemma bs_eval_tendsto {f : ℕ → BFun S} {g : BFun S} (h : Tendsto f atTop (𝓝 g)) (x : S) :
    Tendsto (fun N => f N x) atTop (𝓝 (g x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at h ⊢
  apply squeeze_zero (fun N => norm_nonneg _) _ h
  intro N
  simpa [Real.norm_eq_abs] using bs_abs_le_norm (f N) g x

lemma bs_eval_tendsto' {f : ℕ → BFun S} {g : BFun S} (h : Tendsto f atTop (𝓝 g)) (x : S) :
    Tendsto (fun N => ((f N x : ℝ) : EReal)) atTop (𝓝 ((g x : ℝ) : EReal)) :=
  EReal.tendsto_coe.2 (bs_eval_tendsto h x)

lemma gD_closed (hA5 : P.A5) (hC : P.AssumptionCtilde Bbar m ρ α) : IsClosed (gD P Bbar) := by
  apply IsSeqClosed.isClosed
  intro xs p hs h
  refine ⟨hC.isClosed.mem_of_tendsto h (Eventually.of_forall fun n => (hs n).1), ?_⟩
  exact (hA5 (fun k => toF (xs k)) (toF p) (fun k => (hs k).2)
    (fun x => bs_eval_tendsto' h x)).1

lemma gDs_closed (hA5 : P.A5) (hC : P.AssumptionCtilde Bbar m ρ α) : IsClosed (gDs P Bbar) := by
  apply IsSeqClosed.isClosed
  intro xs p hs h
  refine ⟨hC.isClosed.mem_of_tendsto h (Eventually.of_forall fun n => (hs n).1), ?_⟩
  exact (hA5 (fun k => toF (xs k)) (toF p) (fun k => P.Fstar_subset (hs k).2)
    (fun x => bs_eval_tendsto' h x)).2 (fun k => (hs k).2)

lemma bs_J0_mem (hC : P.AssumptionCtilde Bbar m ρ α) : ∃ J ∈ gDs P Bbar, P.J0 = toF J := by
  obtain ⟨J, hJ, he, hF⟩ := hC.J0_mem
  exact ⟨J, ⟨hJ, he ▸ hF⟩, he⟩

lemma bs_T_fp (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (hC : P.AssumptionCtilde Bbar m ρ α) :
    ∃ Jf ∈ gDs P Bbar, bs_tb hC Jf = Jf ∧ (∀ J ∈ gDs P Bbar, bs_tb hC J = J → J = Jf) ∧
      (∀ J ∈ gDs P Bbar, Tendsto (fun N => (bs_tb hC)^[N] J) atTop (𝓝 Jf)) ∧
      (∀ J ∈ gDs P Bbar, ‖J - Jf‖ * (1 - ρ) ≤ ‖(bs_tb hC)^[m] J - J‖) := by
  obtain ⟨J0', hJ0', -⟩ := bs_J0_mem hC
  exact bs_fp_gen _ (gDs_closed hA5 hC) ⟨J0', hJ0'⟩ _ (fun J hJ => (bs_tb_spec hC J hJ).1) m
    hC.m_pos ρ hC.ρ_pos.le hC.ρ_lt_one (fun J hJ J' hJ' => bs_tb_contr hA2 hA3 hA4 hC J J' hJ hJ')

lemma bs_Tmu_fp (hA5 : P.A5) (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) :
    ∃ Jf ∈ gD P Bbar, bs_tm hC μ Jf = Jf ∧ (∀ J ∈ gD P Bbar, bs_tm hC μ J = J → J = Jf) ∧
      (∀ J ∈ gD P Bbar, Tendsto (fun N => (bs_tm hC μ)^[N] J) atTop (𝓝 Jf)) ∧
      (∀ J ∈ gD P Bbar, ‖J - Jf‖ * (1 - ρ) ≤ ‖(bs_tm hC μ)^[m] J - J‖) := by
  obtain ⟨J0', hJ0', -⟩ := bs_J0_mem hC
  exact bs_fp_gen _ (gD_closed hA5 hC) ⟨J0', gDs_sub hJ0'⟩ _
    (fun J hJ => (bs_tm_spec hC μ J hJ).1) m hC.m_pos
    ρ hC.ρ_pos.le hC.ρ_lt_one (fun J hJ J' hJ' => bs_tm_contr hC μ J J' hJ hJ')

end ModelPart

section Main
variable {S C : Type*} {P : Model S C} {Bbar : Set (BFun S)} {m : ℕ} {ρ α : ℝ}

structure GH (P : Model S C) (Bbar : Set (BFun S)) (m : ℕ) (ρ α : ℝ) : Prop where
  a2 : P.A2
  a3 : P.A3
  a4 : P.A4
  a5 : P.A5
  c : P.AssumptionCtilde Bbar m ρ α

noncomputable def bs_Jt (hH : GH P Bbar m ρ α) : BFun S :=
  Classical.choose (bs_T_fp hH.a2 hH.a3 hH.a4 hH.a5 hH.c)

lemma bs_Jt_spec (hH : GH P Bbar m ρ α) :
    bs_Jt hH ∈ gDs P Bbar ∧ bs_tb hH.c (bs_Jt hH) = bs_Jt hH ∧
      (∀ J ∈ gDs P Bbar, bs_tb hH.c J = J → J = bs_Jt hH) ∧
      (∀ J ∈ gDs P Bbar, Tendsto (fun N => (bs_tb hH.c)^[N] J) atTop (𝓝 (bs_Jt hH))) ∧
      (∀ J ∈ gDs P Bbar, ‖J - bs_Jt hH‖ * (1 - ρ) ≤ ‖(bs_tb hH.c)^[m] J - J‖) :=
  Classical.choose_spec (bs_T_fp hH.a2 hH.a3 hH.a4 hH.a5 hH.c)

noncomputable def bs_Jm (hH : GH P Bbar m ρ α) (μ : P.Sel) : BFun S :=
  Classical.choose (bs_Tmu_fp hH.a5 hH.c μ)

lemma bs_Jm_spec (hH : GH P Bbar m ρ α) (μ : P.Sel) :
    bs_Jm hH μ ∈ gD P Bbar ∧ bs_tm hH.c μ (bs_Jm hH μ) = bs_Jm hH μ ∧
      (∀ J ∈ gD P Bbar, bs_tm hH.c μ J = J → J = bs_Jm hH μ) ∧
      (∀ J ∈ gD P Bbar, Tendsto (fun N => (bs_tm hH.c μ)^[N] J) atTop (𝓝 (bs_Jm hH μ))) ∧
      (∀ J ∈ gD P Bbar, ‖J - bs_Jm hH μ‖ * (1 - ρ) ≤ ‖(bs_tm hH.c μ)^[m] J - J‖) :=
  Classical.choose_spec (bs_Tmu_fp hH.a5 hH.c μ)

lemma bs_tmi_spec (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (k : ℕ) :
    ∀ J ∈ gD P Bbar, (bs_tm hC μ)^[k] J ∈ gD P Bbar ∧
      toF ((bs_tm hC μ)^[k] J) = (P.Tmu μ.1)^[k] (toF J) := by
  induction k with
  | zero => intro J hJ; exact ⟨hJ, rfl⟩
  | succ k ih =>
    intro J hJ
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h1 := ih J hJ
    have h2 := bs_tm_spec hC μ _ h1.1
    exact ⟨h2.1, by rw [h2.2, h1.2]⟩

lemma bs_Jmu_eq (hH : GH P Bbar m ρ α) (μ : P.Sel) :
    P.Jmu μ = toF (bs_Jm hH μ) := by
  obtain ⟨J0', hJ0', hJ0eq⟩ := bs_J0_mem hH.c
  funext x
  have ht := bs_eval_tendsto' ((bs_Jm_spec hH μ).2.2.2.1 J0' (gDs_sub hJ0')) x
  have he : (fun N => P.comp (P.stationary μ) N P.J0 x) =
      fun N => ((((bs_tm hH.c μ)^[N] J0') x : ℝ) : EReal) := by
    funext N
    rw [hJ0eq, ← (bs_cp_spec hH.c _ N J0' (gDs_sub hJ0')).2, bs_cp_stat]
    rfl
  show limUnder atTop (fun N => P.comp (P.stationary μ) N P.J0 x) = _
  rw [he]
  exact ht.limUnder_eq

lemma bs_Jpi_ge (hH : GH P Bbar m ρ α) (π : P.Policy) (x : S) :
    ((bs_Jt hH x : ℝ) : EReal) ≤ P.Jpi π x := by
  obtain ⟨J0', hJ0', hJ0eq⟩ := bs_J0_mem hH.c
  obtain ⟨r, hr⟩ := hH.c.limit_real π x
  have hJ : P.Jpi π x = (r : EReal) := hr.limUnder_eq
  rw [hJ]
  refine le_of_tendsto_of_tendsto' (bs_eval_tendsto' ((bs_Jt_spec hH).2.2.2.1 J0' hJ0') x) hr ?_
  intro N
  show _ ≤ P.comp π N P.J0 x
  rw [hJ0eq, ← (bs_cp_spec hH.c π N J0' (gDs_sub hJ0')).2]
  exact EReal.coe_le_coe_iff.2 (bs_tbi_le hH.a2 hH.a3 hH.c J0' hJ0' N π x)

lemma bs_iter_dist (hC : P.AssumptionCtilde Bbar m ρ α) (μ : P.Sel) (J : BFun S)
    (hJ : J ∈ gD P Bbar) (n : ℕ) :
    ‖(bs_tm hC μ)^[n] J - J‖ ≤ (∑ i ∈ Finset.range n, α ^ i) * ‖bs_tm hC μ J - J‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Finset.sum_range_succ, add_mul]
    have h1 := norm_sub_le_norm_sub_add_norm_sub ((bs_tm hC μ)^[n] (bs_tm hC μ J))
      ((bs_tm hC μ)^[n] J) J
    have h2 := bs_cp_lip hC (P.stationary μ) n _ (bs_tm_spec hC μ J hJ).1 J hJ
    rw [bs_cp_stat, bs_cp_stat] at h2
    linarith

lemma bs_near_opt (hH : GH P Bbar m ρ α) (ε : ℝ) (hε : 0 < ε) :
    ∃ μ : P.Sel, ‖bs_Jm hH μ - bs_Jt hH‖ ≤ ε := by
  obtain ⟨hJt, hfix, -, -, -⟩ := bs_Jt_spec hH
  have hC := hH.c
  set A := ∑ i ∈ Finset.range m, α ^ i with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => pow_nonneg hC.α_pos.le _
  have hρ : 0 < 1 - ρ := by linarith [hC.ρ_lt_one]
  set δ := ε * (1 - ρ) / (A + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨μ, hμ⟩ := bs_tb_approx hH.a4 hH.c _ hJt δ hδ0
  refine ⟨μ, ?_⟩
  have hd : ‖bs_tm hH.c μ (bs_Jt hH) - bs_Jt hH‖ ≤ δ := by
    apply bs_norm_le _ _ _ hδ0.le
    intro x
    have h1 := bs_tb_le hH.c μ _ hJt x
    have h2 := hμ x
    rw [hfix] at h1 h2
    rw [abs_le]; constructor <;> linarith
  have he := (bs_Jm_spec hH μ).2.2.2.2 _ (gDs_sub hJt)
  have hi := bs_iter_dist hH.c μ _ (gDs_sub hJt) m
  have h3 : A * δ ≤ ε * (1 - ρ) := by
    rw [hδ, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith [mul_pos hε hρ]
  have h4 : ‖bs_Jt hH - bs_Jm hH μ‖ * (1 - ρ) ≤ ε * (1 - ρ) := by
    have := mul_le_mul_of_nonneg_left hd hA0
    linarith
  rw [norm_sub_rev]
  exact le_of_mul_le_mul_right h4 hρ

lemma bs_Jstar_eq (hH : GH P Bbar m ρ α) : P.Jstar = toF (bs_Jt hH) := by
  funext x
  apply le_antisymm
  · apply bs_ereal_le_of_eps
    intro ε hε
    obtain ⟨μ, hμ⟩ := bs_near_opt hH ε hε
    have h1 : P.Jstar x ≤ P.Jmu μ x := iInf_le (fun π => P.Jpi π x) (P.stationary μ)
    rw [bs_Jmu_eq hH μ] at h1
    refine h1.trans (EReal.coe_le_coe_iff.2 ?_)
    have := (abs_le.1 (bs_abs_le_norm (bs_Jm hH μ) (bs_Jt hH) x)).2
    linarith
  · exact le_iInf fun π => bs_Jpi_ge hH π x

lemma bs_Jpi_ge_Tmu (hH : GH P Bbar m ρ α) (π : P.Policy) (x : S) :
    ((bs_tm hH.c (π 0) (bs_Jt hH) x : ℝ) : EReal) ≤ P.Jpi π x := by
  have hC := hH.c
  obtain ⟨J0', hJ0', hJ0eq⟩ := bs_J0_mem hC
  obtain ⟨hJt, -, -, htend, -⟩ := bs_Jt_spec hH
  obtain ⟨r, hr⟩ := hC.limit_real π x
  have hJ : P.Jpi π x = (r : EReal) := hr.limUnder_eq
  rw [hJ]
  have hr1 := hr.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun N => bs_tm hH.c (π 0) ((bs_tb hH.c)^[N] J0')) atTop
      (𝓝 (bs_tm hH.c (π 0) (bs_Jt hH))) := by
    have h0 := htend J0' hJ0'
    rw [tendsto_iff_norm_sub_tendsto_zero] at h0 ⊢
    apply squeeze_zero (fun N => norm_nonneg _)
      (fun N => bs_tm_lip hH.c (π 0) _ _ (gDs_sub (bs_tbi_spec hH.c N J0' hJ0').1)
        (gDs_sub hJt))
    simpa using h0.const_mul α
  refine le_of_tendsto_of_tendsto' (bs_eval_tendsto' ht x) hr1 ?_
  intro N
  show _ ≤ P.comp π (N + 1) P.J0 x
  rw [hJ0eq, ← (bs_cp_spec hH.c π (N + 1) J0' (gDs_sub hJ0')).2]
  show _ ≤ ((bs_cp hH.c π (N + 1) J0' x : ℝ) : EReal)
  rw [bs_cp_succ']
  apply EReal.coe_le_coe_iff.2
  exact bs_tm_mono hH.c _ _ _ (gDs_sub (bs_tbi_spec hH.c N J0' hJ0').1)
    (bs_cp_spec hH.c _ N J0' (gDs_sub hJ0')).1 (bs_tbi_le hH.a2 hH.a3 hH.c J0' hJ0' N _) x

end Main

section Final
variable {S C : Type*} {P : Model S C} {Bbar : Set (BFun S)} {m : ℕ} {ρ α : ℝ}

lemma partA (hH : GH P Bbar m ρ α) :
    MemBbarInter Bbar P.Fstar P.Jstar ∧ P.T P.Jstar = P.Jstar ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' = J' → J' = P.Jstar) ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' ≤ J' → P.Jstar ≤ J') ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → J' ≤ P.T J' → J' ≤ P.Jstar) := by
  obtain ⟨hJt, hfix, huniq, htend, -⟩ := bs_Jt_spec hH
  have hJs := bs_Jstar_eq hH
  refine ⟨⟨_, hJt.1, hJs, hJs ▸ hJt.2⟩, ?_, ?_, ?_, ?_⟩
  · rw [hJs, ← (bs_tb_spec hH.c _ hJt).2, hfix]
  · rintro _ ⟨J, hJB, rfl, hJF⟩ h
    have hJ : J ∈ gDs P Bbar := ⟨hJB, hJF⟩
    rw [← (bs_tb_spec hH.c J hJ).2] at h
    rw [hJs, huniq J hJ (bs_toF_injective h)]
  · rintro _ ⟨J, hJB, rfl, hJF⟩ h x
    have hJ : J ∈ gDs P Bbar := ⟨hJB, hJF⟩
    have h1 : ∀ x, bs_tb hH.c J x ≤ J x := fun x => by
      have := h x
      rw [← (bs_tb_spec hH.c J hJ).2] at this
      exact EReal.coe_le_coe_iff.1 this
    have h2 : ∀ N, ∀ x, (bs_tb hH.c)^[N] J x ≤ J x := by
      intro N; induction N with
      | zero => intro x; exact le_rfl
      | succ N ih =>
        intro x
        rw [Function.iterate_succ_apply']
        exact (bs_tb_mono hH.c _ _ (bs_tbi_spec hH.c N J hJ).1 hJ ih x).trans (h1 x)
    rw [hJs]
    exact EReal.coe_le_coe_iff.2 (le_of_tendsto' (bs_eval_tendsto (htend J hJ) x) fun N => h2 N x)
  · rintro _ ⟨J, hJB, rfl, hJF⟩ h x
    have hJ : J ∈ gDs P Bbar := ⟨hJB, hJF⟩
    have h1 : ∀ x, J x ≤ bs_tb hH.c J x := fun x => by
      have := h x
      rw [← (bs_tb_spec hH.c J hJ).2] at this
      exact EReal.coe_le_coe_iff.1 this
    have h2 : ∀ N, ∀ x, J x ≤ (bs_tb hH.c)^[N] J x := by
      intro N; induction N with
      | zero => intro x; exact le_rfl
      | succ N ih =>
        intro x
        rw [Function.iterate_succ_apply']
        exact (h1 x).trans (bs_tb_mono hH.c _ _ hJ (bs_tbi_spec hH.c N J hJ).1 ih x)
    rw [hJs]
    exact EReal.coe_le_coe_iff.2 (ge_of_tendsto' (bs_eval_tendsto (htend J hJ) x) fun N => h2 N x)

lemma partB (hH : GH P Bbar m ρ α) (μ : P.Sel) :
    MemBbarInter Bbar P.Ftil (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.Jmu μ ∧
      ∀ J', MemBbarInter Bbar P.Ftil J' → P.Tmu μ.1 J' = J' → J' = P.Jmu μ := by
  obtain ⟨hJm, hmfix, hmuniq, -, -⟩ := bs_Jm_spec hH μ
  have hJe := bs_Jmu_eq hH μ
  refine ⟨⟨_, hJm.1, hJe, hJe ▸ hJm.2⟩, ?_, ?_⟩
  · rw [hJe, ← (bs_tm_spec hH.c μ _ hJm).2, hmfix]
  · rintro _ ⟨J, hJB, rfl, hJF⟩ h
    have hJ : J ∈ gD P Bbar := ⟨hJB, hJF⟩
    rw [← (bs_tm_spec hH.c μ J hJ).2] at h
    rw [hJe, hmuniq J hJ (bs_toF_injective h)]

lemma partC1 (hH : GH P Bbar m ρ α) : ∀ J, MemBbarInter Bbar P.Fstar J → ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → SupDistLe (P.T^[N] J) P.Jstar ε := by
  rintro _ ⟨J, hJB, rfl, hJF⟩ ε hε
  have hJ : J ∈ gDs P Bbar := ⟨hJB, hJF⟩
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 ((bs_Jt_spec hH).2.2.2.1 J hJ) ε hε
  refine ⟨N0, fun N hN => ?_⟩
  rw [← (bs_tbi_spec hH.c N J hJ).2, bs_Jstar_eq hH, bs_supDist_iff]
  intro x
  have := hN0 N hN
  rw [dist_eq_norm] at this
  exact (bs_abs_le_norm _ _ x).trans this.le

lemma partC2 (hH : GH P Bbar m ρ α) : ∀ μ : P.Sel, ∀ J, MemBbarInter Bbar P.Ftil J →
    ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → SupDistLe ((P.Tmu μ.1)^[N] J) (P.Jmu μ) ε := by
  rintro μ _ ⟨J, hJB, rfl, hJF⟩ ε hε
  have hJ : J ∈ gD P Bbar := ⟨hJB, hJF⟩
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 ((bs_Jm_spec hH μ).2.2.2.1 J hJ) ε hε
  refine ⟨N0, fun N hN => ?_⟩
  rw [← (bs_tmi_spec hH.c μ N J hJ).2, bs_Jmu_eq hH μ, bs_supDist_iff]
  intro x
  have := hN0 N hN
  rw [dist_eq_norm] at this
  exact (bs_abs_le_norm _ _ x).trans this.le

lemma partD (hH : GH P Bbar m ρ α) (μ : P.Sel) :
    (P.IsOptimal (P.stationary μ) ↔ P.Tmu μ.1 P.Jstar = P.T P.Jstar) ∧
      (P.IsOptimal (P.stationary μ) ↔
        MemBbarInter Bbar P.Fstar (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.T (P.Jmu μ)) := by
  obtain ⟨hMem, hfix, huniq, -, -⟩ := partA hH
  obtain ⟨hMemB, hmfix, hmuniq⟩ := partB hH μ
  have hopt : P.IsOptimal (P.stationary μ) ↔ P.Jmu μ = P.Jstar := Iff.rfl
  rw [hopt]
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← h, hmfix, h, hfix]
  · have hMem' : MemBbarInter Bbar P.Ftil P.Jstar := by
      obtain ⟨J, hJB, he, hF⟩ := hMem
      exact ⟨J, hJB, he, P.Fstar_subset hF⟩
    exact (hmuniq _ hMem' (h.trans hfix)).symm
  · rw [h]
    exact ⟨hMem, by rw [hfix, ← h, hmfix]⟩
  · exact huniq _ h.1 (h.2.symm.trans hmfix)

lemma partE (hH : GH P Bbar m ρ α) :
    ∀ ε : ℝ, 0 < ε → ∃ μ : P.Sel, SupDistLe P.Jstar (P.Jmu μ) ε := by
  intro ε hε
  obtain ⟨μ, hμ⟩ := bs_near_opt hH ε hε
  refine ⟨μ, ?_⟩
  rw [bs_Jstar_eq hH, bs_Jmu_eq hH μ, bs_supDist_iff]
  intro x
  rw [norm_sub_rev] at hμ
  exact (bs_abs_le_norm _ _ x).trans hμ

end Final

end G64

theorem p64_core {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) (hC : P.AssumptionCtilde Bbar m ρ α) :
    -- (a)
    (MemBbarInter Bbar P.Fstar P.Jstar ∧ P.T P.Jstar = P.Jstar ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' = J' → J' = P.Jstar) ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' ≤ J' → P.Jstar ≤ J') ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → J' ≤ P.T J' → J' ≤ P.Jstar)) ∧
    -- (b)
    (∀ μ : P.Sel, MemBbarInter Bbar P.Ftil (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.Jmu μ ∧
      ∀ J', MemBbarInter Bbar P.Ftil J' → P.Tmu μ.1 J' = J' → J' = P.Jmu μ) ∧
    -- (c)
    (∀ J, MemBbarInter Bbar P.Fstar J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe (P.T^[N] J) P.Jstar ε) ∧
    (∀ μ : P.Sel, ∀ J, MemBbarInter Bbar P.Ftil J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe ((P.Tmu μ.1)^[N] J) (P.Jmu μ) ε) ∧
    -- (d)
    (∀ μ : P.Sel,
      (P.IsOptimal (P.stationary μ) ↔ P.Tmu μ.1 P.Jstar = P.T P.Jstar) ∧
      (P.IsOptimal (P.stationary μ) ↔
        MemBbarInter Bbar P.Fstar (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.T (P.Jmu μ))) ∧
    -- (e)
    (∀ ε : ℝ, 0 < ε → ∃ μ : P.Sel, BertsekasShreve.Contraction.SupDistLe P.Jstar (P.Jmu μ) ε) := by
  have hH : G64.GH P Bbar m ρ α := ⟨hA2, hA3, hA4, hA5, hC⟩
  exact ⟨G64.partA hH, G64.partB hH, G64.partC1 hH, G64.partC2 hH, G64.partD hH, G64.partE hH⟩

theorem p65a_core {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) (hC : P.AssumptionCtilde Bbar m ρ α)
    (hES : P.ExactSelection)
    (hopt : ∀ x, ∃ π : P.Policy, P.IsOptimalAt π x) :
    ∃ μ : P.Sel, P.IsOptimal (P.stationary μ) := by
  have hH : G64.GH P Bbar m ρ α := ⟨hA2, hA3, hA4, hA5, hC⟩
  obtain ⟨hMem, hfix, -, -, -⟩ := G64.partA hH
  obtain ⟨hJt, -, -, -, -⟩ := G64.bs_Jt_spec hH
  have hJs := G64.bs_Jstar_eq hH
  have hJF : P.Jstar ∈ P.Fstar := by obtain ⟨_, _, _, h⟩ := hMem; exact h
  obtain ⟨μ, hμ, he⟩ := hES _ hJF (fun x => by
    obtain ⟨π, hπ⟩ := hopt x
    refine ⟨(π 0).1 x, P.Mtil_subset _ (π 0).2 x, le_antisymm ?_ ?_⟩
    · have h1 := G64.bs_Jpi_ge_Tmu hH π x
      rw [G64.bs_tm_apply hH.c _ _ (G64.gDs_sub hJt), ← hJs] at h1
      have h2 : P.Jpi π x = P.Jstar x := hπ
      rw [h2] at h1
      calc P.H x ((π 0).1 x) P.Jstar ≤ P.Jstar x := h1
        _ = P.T P.Jstar x := by rw [hfix]
    · exact biInf_le (fun u => P.H x u P.Jstar) (P.Mtil_subset _ (π 0).2 x))
  exact ⟨⟨μ, hμ⟩, ((G64.partD hH ⟨μ, hμ⟩).1).2 he⟩

end BertsekasShreve.Generalized

open BertsekasShreve.Generalized


theorem solution {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hA5 : P.A5)
    (Bbar : Set (BertsekasShreve.Contraction.BFun S)) (m : ℕ) (ρ α : ℝ) (hC : P.AssumptionCtilde Bbar m ρ α) :
    -- (a)
    (MemBbarInter Bbar P.Fstar P.Jstar ∧ P.T P.Jstar = P.Jstar ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' = J' → J' = P.Jstar) ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → P.T J' ≤ J' → P.Jstar ≤ J') ∧
      (∀ J', MemBbarInter Bbar P.Fstar J' → J' ≤ P.T J' → J' ≤ P.Jstar)) ∧
    -- (b)
    (∀ μ : P.Sel, MemBbarInter Bbar P.Ftil (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.Jmu μ ∧
      ∀ J', MemBbarInter Bbar P.Ftil J' → P.Tmu μ.1 J' = J' → J' = P.Jmu μ) ∧
    -- (c)
    (∀ J, MemBbarInter Bbar P.Fstar J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe (P.T^[N] J) P.Jstar ε) ∧
    (∀ μ : P.Sel, ∀ J, MemBbarInter Bbar P.Ftil J → ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → BertsekasShreve.Contraction.SupDistLe ((P.Tmu μ.1)^[N] J) (P.Jmu μ) ε) ∧
    -- (d)
    (∀ μ : P.Sel,
      (P.IsOptimal (P.stationary μ) ↔ P.Tmu μ.1 P.Jstar = P.T P.Jstar) ∧
      (P.IsOptimal (P.stationary μ) ↔
        MemBbarInter Bbar P.Fstar (P.Jmu μ) ∧ P.Tmu μ.1 (P.Jmu μ) = P.T (P.Jmu μ))) ∧
    -- (e)
    (∀ ε : ℝ, 0 < ε → ∃ μ : P.Sel, BertsekasShreve.Contraction.SupDistLe P.Jstar (P.Jmu μ) ε) := by
  exact p64_core P hA1 hA2 hA3 hA4 hA5 Bbar m ρ α hC
