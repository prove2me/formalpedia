-- Prove2me | solution 1 for GenNewtonSubgrad.Composite.proposition_7_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T17:08:20.750598+00:00
-- url     : https://prove2.me/submissions/a87992d7-3aab-4fb8-b650-26b60ea004ed

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Definitions.Def_GenNewtonSubgrad_Composite_Envelope
import Theorems.Thm_GenNewtonSubgrad_Composite_proposition_7_2
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_iii
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_4

open Filter Topology
open scoped InnerProductSpace

namespace GNCAux
open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma quadF_expand (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x h : E) :
    quadF A b α (x + h) = quadF A b α x + ⟪A x + b, h⟫_ℝ + (1/2) * ⟪A h, h⟫_ℝ := by
  have hs : ⟪A h, x⟫_ℝ = ⟪h, A x⟫_ℝ := by
    have := hA.isSymmetric h x
    simpa using this
  simp only [quadF, map_add, inner_add_left, inner_add_right]
  rw [hs, real_inner_comm h (A x)]
  ring

lemma hasGradientAt_quadF (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x : E) :
    HasGradientAt (quadF A b α) (A x + b) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have key : ∀ h : E, quadF A b α (x + h) - quadF A b α x - (InnerProductSpace.toDual ℝ E (A x + b)) h
      = (1/2) * ⟪A h, h⟫_ℝ := by
    intro h
    rw [quadF_expand A hA b α x h, InnerProductSpace.toDual_apply_apply]
    ring
  simp_rw [key]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h : E => ‖h‖ ^ 2) ?_ ?_
  · refine Asymptotics.IsBigO.of_bound (‖A‖ / 2) (Eventually.of_forall fun h => ?_)
    rw [Real.norm_eq_abs, abs_mul, norm_pow, norm_norm]
    have h1 : |⟪A h, h⟫_ℝ| ≤ ‖A‖ * ‖h‖ ^ 2 := by
      calc |⟪A h, h⟫_ℝ| ≤ ‖A h‖ * ‖h‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖A‖ * ‖h‖ * ‖h‖ := by gcongr; exact A.le_opNorm h
        _ = ‖A‖ * ‖h‖ ^ 2 := by ring
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2)]
    nlinarith
  · exact Asymptotics.isLittleO_norm_pow_id (by norm_num : 1 < 2)

lemma gradient_quadF (A : E →L[ℝ] E) (hA : IsSelfAdjoint A) (b : E) (α : ℝ) (x : E) :
    gradient (quadF A b α) x = A x + b :=
  (hasGradientAt_quadF A hA b α x).gradient

lemma contDiff_quadF (A : E →L[ℝ] E) (b : E) (α : ℝ) : ContDiff ℝ 2 (quadF A b α) := by
  unfold quadF
  have h1 : ContDiff ℝ 2 (fun x : E => ⟪A x, x⟫_ℝ) := (A.contDiff).inner ℝ contDiff_id
  have h2 : ContDiff ℝ 2 (fun x : E => ⟪b, x⟫_ℝ) := contDiff_const.inner ℝ contDiff_id
  exact ((contDiff_const.mul h1).add h2).add contDiff_const


end GNCAux

namespace GNC73
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma regN_gen (Φ : E × E → E × E) (Λ : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') {z a : E × E} (hz : z ∈ S) (ha : a ∈ regNormal S' (Φ z)) :
    adjm a ∈ regNormal S z := by
  refine ⟨hz, fun ε hε => ?_⟩
  have hΦc : Continuous Φ := by
    have : Φ = fun w => Φ 0 + Λ w := by
      funext w; have := hΦ w 0; rw [sub_zero] at this; rw [← this]; abel
    rw [this]; exact continuous_const.add Λ.continuous
  have hK : 0 < ‖Λ‖ + 1 := by positivity
  have h1 := ha.2 (ε / (‖Λ‖ + 1)) (div_pos hε hK)
  have h2 := (hΦc.tendsto z).eventually h1
  filter_upwards [h2] with w hw hwS
  have := hw (hS w hwS)
  rw [hadj, ← hΦ]
  refine this.trans ?_
  rw [hΦ]
  calc ε / (‖Λ‖ + 1) * ‖Λ (w - z)‖ ≤ ε / (‖Λ‖ + 1) * ((‖Λ‖ + 1) * ‖w - z‖) := by
        gcongr
        calc ‖Λ (w - z)‖ ≤ ‖Λ‖ * ‖w - z‖ := Λ.le_opNorm _
          _ ≤ (‖Λ‖ + 1) * ‖w - z‖ := by nlinarith [norm_nonneg (w - z)]
    _ = ε * ‖w - z‖ := by field_simp

lemma limN_gen (Φ Ψ : E × E → E × E) (Λ : (E × E) →L[ℝ] (E × E))
    (hΦ : ∀ w z, Φ w - Φ z = Λ (w - z)) (adjm : E × E → E × E)
    (hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h)) (hadjc : Continuous adjm)
    (hΨc : Continuous Ψ) (hΦΨ : ∀ w, Φ (Ψ w) = w) {S S' : Set (E × E)}
    (hS : ∀ w ∈ S, Φ w ∈ S') (hS' : ∀ w ∈ S', Ψ w ∈ S) {z a : E × E} (hz : z ∈ S)
    (hΨΦ : Ψ (Φ z) = z) (ha : a ∈ limNormal S' (Φ z)) : adjm a ∈ limNormal S z := by
  obtain ⟨-, zs, as, hzs, hzl, hal, hreg⟩ := ha
  refine ⟨hz, fun k => Ψ (zs k), fun k => adjm (as k), fun k => hS' _ (hzs k), ?_,
    (hadjc.tendsto a).comp hal, fun k => ?_⟩
  · have := (hΨc.tendsto _).comp hzl
    rwa [hΨΦ] at this
  · apply regN_gen Φ Λ hΦ adjm hadj hS (hS' _ (hzs k))
    rw [hΦΨ]; exact hreg k

lemma regNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N) {z : E × E}
    (hzN : z ∈ N) (a : E × E) : a ∈ regNormal S z → a ∈ regNormal S' z := by
  rintro ⟨hz, h⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  refine ⟨hz', fun ε hε => ?_⟩
  filter_upwards [h ε hε, hN.mem_nhds hzN] with w hw hwN hwS'
  have : w ∈ S' ∩ N := ⟨hwS', hwN⟩
  rw [← hSS] at this
  exact hw this.1

lemma limNormal_local {S S' N : Set (E × E)} (hN : IsOpen N) (hSS : S ∩ N = S' ∩ N) {z : E × E}
    (hzN : z ∈ N) (a : E × E) : a ∈ limNormal S z → a ∈ limNormal S' z := by
  rintro ⟨hz, zs, as, hzs, hzl, hal, hreg⟩
  have hz' : z ∈ S' := by
    have : z ∈ S ∩ N := ⟨hz, hzN⟩
    rw [hSS] at this; exact this.1
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hzl.eventually (hN.mem_nhds hzN))
  have hsh : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
  refine ⟨hz', fun k => zs (k + K), fun k => as (k + K), fun k => ?_, hzl.comp hsh, hal.comp hsh,
    fun k => regNormal_local hN hSS (hK _ (Nat.le_add_left K k)) _ (hreg _)⟩
  have : zs (k + K) ∈ S ∩ N := ⟨hzs _, hK _ (Nat.le_add_left K k)⟩
  rw [hSS] at this; exact this.1

lemma coderiv_congr (F G : E → E) {U : Set E} (hU : IsOpen U) (hFG : ∀ y ∈ U, F y = G y)
    {x : E} (hx : x ∈ U) (w : E) :
    coderiv (sv F) x (F x) w = coderiv (sv G) x (G x) w := by
  have hN : IsOpen (U ×ˢ (Set.univ : Set E)) := hU.prod isOpen_univ
  have hSS : gph (sv F) ∩ U ×ˢ Set.univ = gph (sv G) ∩ U ×ˢ Set.univ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_univ, and_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show p.2 ∈ ({G p.1} : Set E)
      have : p.2 ∈ ({F p.1} : Set E) := h1
      rwa [hFG p.1 h2] at this
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      show p.2 ∈ ({F p.1} : Set E)
      have : p.2 ∈ ({G p.1} : Set E) := h1
      rwa [← hFG p.1 h2] at this
  have hzN : ((x, F x) : E × E) ∈ U ×ˢ (Set.univ : Set E) := ⟨hx, Set.mem_univ _⟩
  ext u
  show (u, -w) ∈ limNormal (gph (sv F)) (x, F x) ↔ (u, -w) ∈ limNormal (gph (sv G)) (x, G x)
  rw [← hFG x hx]
  exact ⟨limNormal_local hN hSS hzN _, limNormal_local hN hSS.symm hzN _⟩

end GNC73

open GenNewtonSubgrad.Composite GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared GNCAux GNC73 in
theorem solution {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsSelfAdjoint A)
    (b : EuclideanSpace ℝ (Fin n)) (α : ℝ) (g : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hg : GenNewtonSubgrad.ProxReg.IsProperFn g) (hpb : GenNewtonSubgrad.ProxReg.IsProxBounded g)
    (hpr : GenNewtonSubgrad.ProxReg.IsContProxRegularAt g xbar (-(A xbar + b)) r ε)
    (hstat : 0 ∈ NonconvexSplitting.Shared.LimitingSubdiff (sumFn (quadF A b α) g) xbar) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ γ₀ ≤ r⁻¹ ∧ ∀ γ : ℝ, 0 < γ → γ < γ₀ →
      Function.Bijective (shiftOp A γ) →
      ∃ U ∈ 𝓝 xbar, ∀ x ∈ U,
        (fbe (quadF A b α) g γ x ≠ ⊤ ∧ fbe (quadF A b α) g γ x ≠ ⊥ ∧
          DifferentiableAt ℝ (fun y => (fbe (quadF A b α) g γ y).toReal) x) ∧
        ∃ p : EuclideanSpace ℝ (Fin n), GenNewtonSubgrad.ProxReg.prox g γ (x - γ • (A x + b)) = {p} ∧
        ∀ w z : EuclideanSpace ℝ (Fin n),
          z ∈ GenNewtonSubgrad.ProxReg.coderiv (GenNewtonSubgrad.ProxReg.sv (gradient (fun y => (fbe (quadF A b α) g γ y).toReal))) x
              (gradient (fun y => (fbe (quadF A b α) g γ y).toReal) x) w ↔
            shiftInv A γ z - A w ∈
              GenNewtonSubgrad.ProxReg.secondSubdiff g p (γ⁻¹ • ((x - γ • (A x + b)) - p)) (w - γ • shiftInv A γ z) := by
  classical
  have hgrad : ∀ x, gradient (quadF A b α) x = A x + b := gradient_quadF A hA b α
  have hfd : ∀ x, fderiv ℝ (gradient (quadF A b α)) x = A := by
    intro x
    have : gradient (quadF A b α) = fun y => A y + b := funext hgrad
    rw [this]; exact (A.hasFDerivAt.add_const b).fderiv
  have hAs : ∀ h k, ⟪A h, k⟫_ℝ = ⟪h, A k⟫_ℝ := fun h k => by simpa using hA.isSymmetric h k
  set vbar := -(A xbar + b) with hvbar
  obtain ⟨γ2, hγ2, hγ2r, h72⟩ := proposition_7_2 (quadF A b α) g xbar r ε
    ⟨Set.univ, Filter.univ_mem, (contDiff_quadF A b α).contDiffOn⟩ hstat hg hpb
    (by rw [hgrad]; exact hpr)
  obtain ⟨l3, hl3, -, H3⟩ := lemma_6_3_iii g xbar vbar r ε hg hpb hpr
  obtain ⟨l4, hl4, -, H4⟩ := lemma_6_4 g xbar vbar r ε hg hpb hpr
  refine ⟨min γ2 (min l3 l4), lt_min hγ2 (lt_min hl3 hl4), (min_le_left _ _).trans hγ2r,
    fun γ hγ hlt hB => ?_⟩
  have lt2 : γ < γ2 := lt_of_lt_of_le hlt (min_le_left _ _)
  have lt3 : γ < l3 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have lt4 : γ < l4 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨U2, hU2, P, hP, -, hfin2, hdiff2, -, hform, -⟩ := h72 γ hγ lt2
  obtain ⟨W3, hW3, -, -, hgr3, -⟩ := H3 γ hγ lt3
  obtain ⟨W4, hW4, -, h64⟩ := H4 γ hγ lt4
  -- the operator B and its inverse
  set B := shiftOp A γ with hBdef
  have hBapp : ∀ y, B y = y - γ • A y := by intro y; simp [hBdef, shiftOp]
  set Be := ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.2 hB.1)
    (LinearMap.range_eq_top.2 hB.2) with hBe
  set Binv : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := (Be.symm : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) with hBinv
  have hBBi : ∀ y, B (Binv y) = y := fun y =>
    ContinuousLinearEquiv.ofBijective_apply_symm_apply B _ _ y
  have hBiB : ∀ y, Binv (B y) = y := fun y =>
    ContinuousLinearEquiv.ofBijective_symm_apply_apply B _ _ y
  have hsinv : ∀ z, shiftInv A γ z = Binv z := by
    intro z
    apply hB.1
    rw [hBBi]
    exact Function.rightInverse_invFun hB.2 z
  have hAB : ∀ y, A (B y) = B (A y) := by
    intro y; rw [hBapp, hBapp, map_sub, map_smul]
  have hABi : ∀ y, A (Binv y) = Binv (A y) := by
    intro y
    have : A y = B (A (Binv y)) := by rw [← hAB, hBBi]
    rw [this, hBiB]
  have hBs : ∀ h k, ⟪B h, k⟫_ℝ = ⟪h, B k⟫_ℝ := by
    intro h k
    rw [hBapp, hBapp, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hAs]
    simp
  have hBis : ∀ h k, ⟪Binv h, k⟫_ℝ = ⟪h, Binv k⟫_ℝ := by
    intro h k
    conv_lhs => rw [← hBBi k]
    rw [← hBs, hBBi]
  -- the envelope
  set e : EuclideanSpace ℝ (Fin n) → ℝ := fun z => (moreauEnv g γ z).toReal with hedef
  set ge := gradient e with hgedef
  set T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => x - γ • (A x + b)
    with hTdef
  have hTB : ∀ x, T x = B x - γ • b := by
    intro x; simp only [hTdef, hBapp, smul_add]; abel
  have hTx : T xbar = xbar + γ • vbar := by
    simp only [hTdef, hvbar, smul_neg, sub_eq_add_neg]
  have hTc : Continuous T := by
    simp only [hTdef]; fun_prop
  set U := interior (U2 ∩ T ⁻¹' (W3 ∩ W4)) with hUdef
  have hUnhds : U ∈ 𝓝 xbar := by
    rw [hUdef, interior_mem_nhds]
    refine Filter.inter_mem hU2 (hTc.continuousAt.preimage_mem_nhds ?_)
    rw [hTx]; exact Filter.inter_mem hW3 hW4
  have hUopen : IsOpen U := isOpen_interior
  have mU2 : ∀ y ∈ U, y ∈ U2 := fun y hy => (interior_subset hy).1
  have mW3 : ∀ y ∈ U, T y ∈ W3 := fun y hy => (interior_subset hy).2.1
  have mW4 : ∀ y ∈ U, T y ∈ W4 := fun y hy => (interior_subset hy).2.2
  have hP' : ∀ y ∈ U2, prox g γ (y - γ • (A y + b)) = {P y} := by
    intro y hy; have := hP y hy; rwa [hgrad] at this
  have hPmem : ∀ y ∈ U2, P y ∈ prox g γ (T y) := by
    intro y hy; rw [hP' y hy]; exact Set.mem_singleton _
  have hge : ∀ y ∈ U, ge (T y) = γ⁻¹ • (T y - P y) := fun y hy =>
    ((hgr3 (T y) (mW3 y hy)).2 (P y) (hPmem y (mU2 y hy))).gradient
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun y => (fbe (quadF A b α) g γ y).toReal with hψdef
  set G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun x => B (ge (T x) + (A x + b))
    with hGdef
  have hψG : ∀ y ∈ U, gradient ψ y = G y := by
    intro y hy
    rw [hform y (mU2 y hy), hfd]
    simp only [hGdef]
    rw [hge y hy]
    have e1 : γ⁻¹ • (T y - P y) + (A y + b) = γ⁻¹ • (y - P y) := by
      simp only [hTdef]
      rw [show y - γ • (A y + b) - P y = (y - P y) - γ • (A y + b) by abel, smul_sub, smul_smul,
        inv_mul_cancel₀ hγ.ne', one_smul]
      abel
    rw [e1, map_smul, hBapp]
  -- graph maps
  set Φ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun q => (Binv (q.1 + γ • b), B (q.2 + A (Binv (q.1 + γ • b)) + b)) with hΦdef
  set Ψ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun q => (T q.1, Binv q.2 - (A q.1 + b)) with hΨdef
  set Λ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (Binv.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      (B.comp (ContinuousLinearMap.snd ℝ _ _ + A.comp (Binv.comp (ContinuousLinearMap.fst ℝ _ _))))
    with hΛdef
  set Λ' : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (B.comp (ContinuousLinearMap.fst ℝ _ _)).prod
      (Binv.comp (ContinuousLinearMap.snd ℝ _ _) - A.comp (ContinuousLinearMap.fst ℝ _ _))
    with hΛ'def
  set adjm : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun a => (Binv a.1 + Binv (A (B a.2)), B a.2) with hadjdef
  set adjm' : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun a => (B a.1 - A a.2, Binv a.2) with hadj'def
  have hΦΛ : ∀ w z, Φ w - Φ z = Λ (w - z) := by
    intro w z
    simp only [hΦdef, hΛdef, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.add_apply,
      Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub, map_sub, map_add]
    refine Prod.ext ?_ ?_ <;> simp only <;> abel
  have hΨΛ : ∀ w z, Ψ w - Ψ z = Λ' (w - z) := by
    intro w z
    simp only [hΨdef, hΛ'def, hTB, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.sub_apply,
      Prod.mk_sub_mk, Prod.fst_sub, Prod.snd_sub, map_sub, map_add]
    refine Prod.ext ?_ ?_ <;> simp only <;> abel
  have hadj : ∀ a h, pairInner (adjm a) h = pairInner a (Λ h) := by
    intro a h
    simp only [pairInner, hadjdef, hΛdef, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.add_apply, inner_add_left, inner_add_right]
    rw [hBis, hBis, hAs, hBs, hBs, map_add, inner_add_right]
    ring
  have hadj' : ∀ a h, pairInner (adjm' a) h = pairInner a (Λ' h) := by
    intro a h
    simp only [pairInner, hadj'def, hΛ'def, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [hBs, hBis, hAs]
    ring
  have hadjc : Continuous adjm := by simp only [hadjdef]; fun_prop
  have hadjc' : Continuous adjm' := by simp only [hadj'def]; fun_prop
  have hΦc : Continuous Φ := by simp only [hΦdef]; fun_prop
  have hΨc : Continuous Ψ := by simp only [hΨdef]; fun_prop
  have hΦΨ : ∀ q, Φ (Ψ q) = q := by
    intro q
    simp only [hΦdef, hΨdef, hTB]
    rw [show B q.1 - γ • b + γ • b = B q.1 by abel, hBiB]
    refine Prod.ext rfl ?_
    simp only
    rw [show Binv q.2 - (A q.1 + b) + A q.1 + b = Binv q.2 by abel, hBBi]
  have hΨΦ : ∀ q, Ψ (Φ q) = q := by
    intro q
    simp only [hΦdef, hΨdef, hTB, hBBi]
    refine Prod.ext (by simp) ?_
    simp only
    rw [hBiB]; abel
  have hSS : ∀ q ∈ gph (sv ge), Φ q ∈ gph (sv G) := by
    intro q hq
    have hq2 : q.2 = ge q.1 := hq
    show B (q.2 + A (Binv (q.1 + γ • b)) + b) ∈ ({G (Binv (q.1 + γ • b))} : Set _)
    have hT : T (Binv (q.1 + γ • b)) = q.1 := by rw [hTB, hBBi]; abel
    simp only [hGdef, hT, hq2, Set.mem_singleton_iff]
    congr 1; abel
  have hSS' : ∀ q ∈ gph (sv G), Ψ q ∈ gph (sv ge) := by
    intro q hq
    have hq2 : q.2 = G q.1 := hq
    show Binv q.2 - (A q.1 + b) ∈ ({ge (T q.1)} : Set _)
    simp only [hq2, hGdef, hBiB, Set.mem_singleton_iff]
    abel
  refine ⟨U, hUnhds, fun x hx => ⟨⟨(hfin2 x (mU2 x hx)).1, (hfin2 x (mU2 x hx)).2,
    hdiff2 x (mU2 x hx)⟩, P x, hP' x (mU2 x hx), fun w z => ?_⟩⟩
  set u := T x with hu
  have hz0 : ((u, ge u) : _ × _) ∈ gph (sv ge) := Set.mem_singleton _
  have hΦz : Φ (u, ge u) = (x, G x) := by
    have h1 : Binv (u + γ • b) = x := by rw [hu, hTB]; rw [show B x - γ • b + γ • b = B x by abel, hBiB]
    simp only [hΦdef, h1, hGdef, ← hu]
    congr 1; congr 1; abel
  have hGx : ((x, G x) : _ × _) ∈ gph (sv G) := Set.mem_singleton _
  rw [coderiv_congr (gradient ψ) G hUopen hψG hx w, hsinv]
  have key : z ∈ coderiv (sv G) x (G x) w ↔ Binv z - A w ∈ coderiv (sv ge) u (ge u) (B w) := by
    constructor
    · intro hzw
      have h1 : ((z, -w) : _ × _) ∈ limNormal (gph (sv G)) (Φ (u, ge u)) := by rw [hΦz]; exact hzw
      have h2 := limN_gen Φ Ψ Λ hΦΛ adjm hadj hadjc hΨc hΦΨ hSS hSS' hz0 (hΨΦ _) h1
      have e : adjm ((z, -w) : _ × _) = (Binv z - A w, -(B w)) := by
        simp only [hadjdef, map_neg]
        refine Prod.ext ?_ rfl
        simp only
        rw [hAB, hBiB]; abel
      rw [e] at h2; exact h2
    · intro hzw
      have h1 : ((Binv z - A w, -(B w)) : _ × _) ∈ limNormal (gph (sv ge)) (Ψ (x, G x)) := by
        rw [← hΦz, hΨΦ]; exact hzw
      have h2 := limN_gen Ψ Φ Λ' hΨΛ adjm' hadj' hadjc' hΦc hΨΦ hSS' hSS hGx
        (by rw [← hΦz, hΨΦ]) h1
      have e : adjm' ((Binv z - A w, -(B w)) : _ × _) = (z, -w) := by
        simp only [hadj'def, map_neg, map_sub, hBBi, hBiB]
        refine Prod.ext ?_ rfl
        simp only
        rw [hAB]; abel
      rw [e] at h2; exact h2
  rw [key, h64 u (mW4 x hx)]
  have hgeu : ge u = γ⁻¹ • (u - P x) := hge x hx
  have hp1 : u - γ • ge u = P x := by
    rw [hgeu, smul_smul, mul_inv_cancel₀ hγ.ne', one_smul]; abel
  have hdir : B w - γ • (Binv z - A w) = w - γ • Binv z := by
    rw [hBapp, smul_sub]; abel
  rw [hp1, hgeu, hdir]
