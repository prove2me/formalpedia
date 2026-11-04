-- Prove2me | solution 1 for DRUQChance.Markov.conic_certificate_essStrict
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:08:51.668763+00:00
-- url     : https://prove2.me/submissions/b2cba544-7b9a-407b-88bc-5ef712dc971b

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic
import Theorems.Thm_SmaleNinth_lp_strong_duality

open Matrix DRConvexOpt.Reform DRUQChance.Markov

/-- Lagrangian relaxation of the non-polyhedral cone constraint (Slater-type separation). -/
theorem DRUQConicAux.step1 {Ω : Type*} {m : ℕ} (P : Set Ω) (yf : Ω → (Fin m → ℝ)) (q : Ω → ℝ)
    (hconvS : Convex ℝ ((fun ω => (yf ω, q ω)) '' P))
    (Kn : Set (Fin m → ℝ)) (hKconv : Convex ℝ Kn)
    (hKsm : ∀ y ∈ Kn, ∀ a : ℝ, 0 ≤ a → a • y ∈ Kn)
    (ω0 : Ω) (hω0P : ω0 ∈ P) (hω0K : yf ω0 ∈ interior Kn) (t : ℝ)
    (hst : ∀ ω ∈ P, yf ω ∈ Kn → q ω ≤ t) :
    ∃ ψn : Fin m → ℝ, (∀ x ∈ Kn, 0 ≤ x ⬝ᵥ ψn) ∧ ∀ ω ∈ P, q ω + yf ω ⬝ᵥ ψn ≤ t := by
  set O : Set ((Fin m → ℝ) × ℝ) := interior Kn ×ˢ Set.Ioi t with hO
  set S : Set ((Fin m → ℝ) × ℝ) := (fun ω => (yf ω, q ω)) '' P with hS
  have hOconv : Convex ℝ O := hKconv.interior.prod (convex_Ioi t)
  have hOopen : IsOpen O := isOpen_interior.prod isOpen_Ioi
  have hdisj : Disjoint O S := by
    rw [Set.disjoint_left]
    rintro ⟨w, a⟩ ⟨hw, ha⟩ ⟨ω, hω, hωe⟩
    simp only [Prod.mk.injEq] at hωe
    obtain ⟨rfl, rfl⟩ := hωe
    have := hst ω hω (interior_subset hw)
    simp only [Set.mem_Ioi] at ha
    linarith
  obtain ⟨f, u, hfO, hfS⟩ := geometric_hahn_banach_open hOconv hOopen hconvS hdisj
  have hf : ∀ (w : Fin m → ℝ) (a : ℝ), f (w, a) = f (w, 0) + a * f (0, 1) := by
    intro w a
    have : ((w, a) : (Fin m → ℝ) × ℝ) = (w, 0) + a • ((0 : Fin m → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set θ := f (0, 1) with hθ
  set g' : (Fin m → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) ℝ) with hg'
  have hg'apply : ∀ w, g' w = f (w, 0) := fun w => rfl
  -- closure of `O`
  have hKsub : Kn ⊆ closure (interior Kn) := by
    rw [hKconv.closure_interior_eq_closure_of_nonempty_interior ⟨_, hω0K⟩]
    exact subset_closure
  have hclO : ∀ k ∈ Kn, ∀ a, t ≤ a → f (k, a) ≤ u := by
    intro k hk a ha
    have hmem : (k, a) ∈ closure O := by
      rw [hO, closure_prod_eq, closure_Ioi]
      exact ⟨hKsub hk, ha⟩
    have hcl : closure O ⊆ {x | f x ≤ u} :=
      closure_minimal (fun x hx => (hfO x hx).le) (isClosed_le f.continuous continuous_const)
    exact hcl hmem
  have h0K : (0 : Fin m → ℝ) ∈ Kn := by
    have := hKsm _ (interior_subset hω0K) 0 le_rfl
    simpa using this
  have hg0 : f (0, 0) = 0 := by
    have : ((0 : Fin m → ℝ), (0 : ℝ)) = 0 := rfl
    rw [this, map_zero]
  -- θ ≤ 0
  have hθle : θ ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set a := max t (u / θ + 1) with ha
    have h1 := hclO 0 h0K a (le_max_left _ _)
    rw [hf, hg0, zero_add] at h1
    have h2 : u / θ + 1 ≤ a := le_max_right _ _
    have h3 : (u / θ + 1) * θ ≤ a * θ := mul_le_mul_of_nonneg_right h2 hpos.le
    rw [add_mul, div_mul_cancel₀ _ hpos.ne'] at h3
    linarith
  -- g ≤ 0 on Kn
  have hgK : ∀ k ∈ Kn, f (k, 0) ≤ 0 := by
    intro k hk
    by_contra hpos
    rw [not_le] at hpos
    set l := (|u - t * θ| + 1) / f (k, 0) with hl
    have hl0 : 0 < l := div_pos (by positivity) hpos
    have h1 := hclO (l • k) (hKsm k hk l hl0.le) t le_rfl
    rw [hf] at h1
    have e : f (l • k, 0) = l * f (k, 0) := by
      have : ((l • k, (0 : ℝ)) : (Fin m → ℝ) × ℝ) = l • (k, 0) := by ext <;> simp
      rw [this, map_smul, smul_eq_mul]
    rw [e, hl, div_mul_cancel₀ _ hpos.ne'] at h1
    have := le_abs_self (u - t * θ)
    linarith
  have htθ : t * θ ≤ u := by
    have h1 := hclO 0 h0K t le_rfl
    rwa [hf, hg0, zero_add] at h1
  have hθlt : θ < 0 := by
    rcases hθle.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hfO (yf ω0, t + 1) ⟨hω0K, by simp⟩
      have h2 := hfS (yf ω0, q ω0) ⟨ω0, hω0P, rfl⟩
      rw [hf] at h1 h2
      rw [h] at h1 h2
      linarith
  -- represent `g` by a vector
  set v : Fin m → ℝ := fun i => g' (fun j => if i = j then 1 else 0) with hv
  have hgv : ∀ w, f (w, 0) = w ⬝ᵥ v := by
    intro w
    rw [← hg'apply]
    have := (g' : (Fin m → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ w
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    simp [dotProduct, hv, smul_eq_mul]
  refine ⟨θ⁻¹ • v, ?_, ?_⟩
  · intro x hx
    rw [dotProduct_smul, smul_eq_mul, ← hgv]
    exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr hθle) (hgK x hx)
  · intro ω hω
    have h2 := hfS (yf ω, q ω) ⟨ω, hω, rfl⟩
    rw [hf, hgv] at h2
    rw [dotProduct_smul, smul_eq_mul]
    have hw : θ⁻¹ < 0 := inv_lt_zero.mpr hθlt
    have h3 : t * θ ≤ yf ω ⬝ᵥ v + q ω * θ := le_trans htθ h2
    have h4 := mul_le_mul_of_nonpos_left h3 hw.le
    have hθ0 : θ ≠ 0 := hθlt.ne
    have e1 : θ⁻¹ * (t * θ) = t := by
      rw [mul_comm t θ, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul]
    have e2 : θ⁻¹ * (yf ω ⬝ᵥ v + q ω * θ) = θ⁻¹ * (yf ω ⬝ᵥ v) + q ω := by
      rw [mul_add, mul_comm (q ω) θ, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul]
    linarith

theorem solution {nP nQ m : ℕ} (C : Matrix (Fin m) (Fin nP) ℝ)
    (D : Matrix (Fin m) (Fin nQ) ℝ) (c : Fin m → ℝ) (K : Set (Fin m → ℝ))
    (hE : EssStrictFeas C D c K) (s : Fin nP → ℝ) (t : ℝ)
    (hst : ∀ ω ∈ confSet C D c K, s ⬝ᵥ ω.1 ≤ t) :
    ∃ ψ ∈ dualCone K, Cᵀ *ᵥ ψ = s ∧ Dᵀ *ᵥ ψ = 0 ∧ c ⬝ᵥ ψ ≤ t := by
  obtain ⟨r, G, Kn, hKc, hKconv, hKsm, hKeq, ω0, hω0p, hω0n⟩ := hE
  set yf : (Fin nP → ℝ) × (Fin nQ → ℝ) → (Fin m → ℝ) := fun ω => c - (C *ᵥ ω.1 + D *ᵥ ω.2)
    with hyf
  set P : Set ((Fin nP → ℝ) × (Fin nQ → ℝ)) := {ω | ∀ k, 0 ≤ (G *ᵥ yf ω) k} with hP
  have hyaff : ∀ (ω ω' : (Fin nP → ℝ) × (Fin nQ → ℝ)) (a b : ℝ), a + b = 1 →
      yf (a • ω + b • ω') = a • yf ω + b • yf ω' := by
    intro ω ω' a b hab
    simp only [hyf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
      mulVec_smul]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : c i = a * c i + b * c i := by rw [← add_mul, hab, one_mul]
    linarith
  have hconvS : Convex ℝ ((fun ω => (yf ω, s ⬝ᵥ ω.1)) '' P) := by
    rintro _ ⟨ω, hω, rfl⟩ _ ⟨ω', hω', rfl⟩ a b ha hb hab
    refine ⟨a • ω + b • ω', ?_, ?_⟩
    · intro k
      rw [hyaff ω ω' a b hab, mulVec_add, mulVec_smul, mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hω k)) (mul_nonneg hb (hω' k))
    · simp only [hyaff ω ω' a b hab, Prod.smul_mk, Prod.mk_add_mk, Prod.fst_add, Prod.smul_fst,
        dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hstP : ∀ ω ∈ P, yf ω ∈ Kn → s ⬝ᵥ ω.1 ≤ t := by
    intro ω hω hK
    apply hst ω
    show c - (C *ᵥ ω.1 + D *ᵥ ω.2) ∈ K
    rw [hKeq]; exact ⟨hω, hK⟩
  obtain ⟨ψn, hψnK, hψnP⟩ := DRUQConicAux.step1 P yf (fun ω => s ⬝ᵥ ω.1) hconvS Kn hKconv hKsm
    ω0 hω0p hω0n t hstP
  -- LP part
  set zx : (Fin (nP + nQ) → ℝ) → (Fin nP → ℝ) := fun x a => x (Fin.castAdd nQ a) with hzx
  set ux : (Fin (nP + nQ) → ℝ) → (Fin nQ → ℝ) := fun x b => x (Fin.natAdd nP b) with hux
  set M : Matrix (Fin r) (Fin (nP + nQ)) ℝ :=
    Matrix.of fun i => Fin.append (fun a => -((G * C) i a)) (fun b => -((G * D) i b)) with hM
  set bb : Fin r → ℝ := -(G *ᵥ c) with hbb
  set cc : Fin (nP + nQ) → ℝ := Fin.append (fun a => -(s - Cᵀ *ᵥ ψn) a) (fun b => (Dᵀ *ᵥ ψn) b) with hcc
  have hMx : ∀ x i, (M *ᵥ x) i = -(((G * C) *ᵥ zx x) i + ((G * D) *ᵥ ux x) i) := by
    intro x i
    simp only [mulVec, dotProduct, hM, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, hzx, hux]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]
  have hccx : ∀ x, ∑ k, cc k * x k = -((s - Cᵀ *ᵥ ψn) ⬝ᵥ zx x) + (Dᵀ *ᵥ ψn) ⬝ᵥ ux x := by
    intro x
    simp only [hcc, Fin.sum_univ_add, Fin.append_left, Fin.append_right, dotProduct, hzx, hux,
      neg_mul, Finset.sum_neg_distrib]
  have hpoly : ∀ x, x ∈ LinearOptimization.polyhedron M bb ↔ (zx x, ux x) ∈ P := by
    intro x
    simp only [LinearOptimization.polyhedron, Set.mem_ofPred_eq, hP, Pi.le_def]
    apply forall_congr'
    intro i
    have e := hMx x i
    rw [← mulVec_mulVec, ← mulVec_mulVec] at e
    show bb i ≤ (M *ᵥ x) i ↔ _
    rw [e]
    simp only [hyf, hbb, mulVec_sub, mulVec_add, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
    constructor <;> intro h <;> linarith
  have hfeas : (LinearOptimization.polyhedron M bb).Nonempty := by
    refine ⟨Fin.append ω0.1 ω0.2, (hpoly _).mpr ?_⟩
    have e1 : zx (Fin.append ω0.1 ω0.2) = ω0.1 := by
      funext a; simp [hzx, Fin.append_left]
    have e2 : ux (Fin.append ω0.1 ω0.2) = ω0.2 := by
      funext b; simp [hux, Fin.append_right]
    rw [e1, e2]; exact hω0p
  have hTr : ∀ {k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (z : Fin k → ℝ),
      (A *ᵥ z) ⬝ᵥ ψn = (Aᵀ *ᵥ ψn) ⬝ᵥ z := by
    intro k A z
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  have hbdd' : ∀ x ∈ LinearOptimization.polyhedron M bb, ψn ⬝ᵥ c - t ≤ ∑ k, cc k * x k := by
    intro x hx
    have h := hψnP (zx x, ux x) ((hpoly x).mp hx)
    rw [hccx]
    simp only [hyf] at h
    rw [sub_dotProduct, add_dotProduct, hTr, hTr] at h
    rw [sub_dotProduct]
    have := dotProduct_comm c ψn
    linarith
  have hbdd : ∃ v : ℝ, ∀ x ∈ LinearOptimization.polyhedron M bb, v ≤ ∑ k, cc k * x k :=
    ⟨_, hbdd'⟩
  obtain ⟨xs, y, hxs, hy0, hyM, hval, -⟩ := SmaleNinth.lp_strong_duality M bb cc hfeas hbdd
  set w := Gᵀ *ᵥ y with hw
  have hCw : Cᵀ *ᵥ w = s - Cᵀ *ᵥ ψn := by
    funext a
    have h := hyM (Fin.castAdd nQ a)
    simp only [hM, hcc, Matrix.of_apply, Fin.append_left, mul_neg, Finset.sum_neg_distrib] at h
    rw [hw, mulVec_mulVec, ← transpose_mul]
    have e : ((G * C)ᵀ *ᵥ y) a = ∑ i, y i * (G * C) i a := by
      simp only [mulVec, dotProduct, transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e]; linarith
  have hDw : Dᵀ *ᵥ w = -(Dᵀ *ᵥ ψn) := by
    funext b
    have h := hyM (Fin.natAdd nP b)
    simp only [hM, hcc, Matrix.of_apply, Fin.append_right, mul_neg, Finset.sum_neg_distrib] at h
    rw [hw, mulVec_mulVec, ← transpose_mul, Pi.neg_apply]
    have e : ((G * D)ᵀ *ᵥ y) b = ∑ i, y i * (G * D) i b := by
      simp only [mulVec, dotProduct, transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e]; linarith
  have hcw : c ⬝ᵥ w ≤ t - ψn ⬝ᵥ c := by
    have h1 := hbdd' xs hxs
    rw [hval] at h1
    have e : c ⬝ᵥ w = -∑ i, y i * bb i := by
      rw [hw, dotProduct_mulVec, vecMul_transpose, hbb]
      simp only [dotProduct, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_neg]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e]; linarith
  refine ⟨ψn + w, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hKeq] at hx
    obtain ⟨hxp, hxn⟩ := hx
    rw [dotProduct_add]
    apply add_nonneg (hψnK x hxn)
    rw [hw, dotProduct_mulVec, vecMul_transpose]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hxp i) (hy0 i))
  · rw [mulVec_add, hCw]; abel
  · rw [mulVec_add, hDw]; abel
  · rw [dotProduct_add]; have := dotProduct_comm c ψn; linarith
