-- Prove2me | solution 1 for DRUQChance.Markov.theorem_3_markov
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T00:20:20.492915+00:00
-- url     : https://prove2.me/submissions/9ea8f09c-ea2c-42e4-8ffc-d2be831607d9

import Mathlib
import Definitions.Def_DRConvexOpt_Reform_Setting
import Definitions.Def_DRUQChance_Markov_Basic
import Theorems.Thm_SmaleNinth_lp_strong_duality
import Theorems.Thm_DRUQChance_Markov_theorem_3_if

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

theorem DRUQConicAux.conic_gen {nP nQ m r e : ℕ} (C : Matrix (Fin m) (Fin nP) ℝ)
    (D : Matrix (Fin m) (Fin nQ) ℝ) (c : Fin m → ℝ) (G : Matrix (Fin r) (Fin m) ℝ)
    (Kn : Set (Fin m → ℝ)) (hKconv : Convex ℝ Kn)
    (hKsm : ∀ y ∈ Kn, ∀ a : ℝ, 0 ≤ a → a • y ∈ Kn)
    (E : Matrix (Fin e) (Fin nP) ℝ) (F : Matrix (Fin e) (Fin nQ) ℝ) (ee : Fin e → ℝ)
    (ω0 : (Fin nP → ℝ) × (Fin nQ → ℝ))
    (hω0p : ∀ k, 0 ≤ (G *ᵥ (c - (C *ᵥ ω0.1 + D *ᵥ ω0.2))) k)
    (hω0n : c - (C *ᵥ ω0.1 + D *ᵥ ω0.2) ∈ interior Kn)
    (hω0e : ∀ i, (E *ᵥ ω0.1 + F *ᵥ ω0.2) i ≤ ee i)
    (a : Fin nP → ℝ) (b : Fin nQ → ℝ) (δ : ℝ)
    (hst : ∀ ω : (Fin nP → ℝ) × (Fin nQ → ℝ),
      (∀ k, 0 ≤ (G *ᵥ (c - (C *ᵥ ω.1 + D *ᵥ ω.2))) k) → c - (C *ᵥ ω.1 + D *ᵥ ω.2) ∈ Kn →
      (∀ i, (E *ᵥ ω.1 + F *ᵥ ω.2) i ≤ ee i) → a ⬝ᵥ ω.1 + b ⬝ᵥ ω.2 ≤ δ) :
    ∃ (ψ : Fin m → ℝ) (ν : Fin e → ℝ),
      (∀ x, (∀ k, 0 ≤ (G *ᵥ x) k) → x ∈ Kn → 0 ≤ x ⬝ᵥ ψ) ∧ (∀ i, 0 ≤ ν i) ∧
      Cᵀ *ᵥ ψ + Eᵀ *ᵥ ν = a ∧ Dᵀ *ᵥ ψ + Fᵀ *ᵥ ν = b ∧ c ⬝ᵥ ψ + ee ⬝ᵥ ν ≤ δ := by
  set yf : (Fin nP → ℝ) × (Fin nQ → ℝ) → (Fin m → ℝ) := fun ω => c - (C *ᵥ ω.1 + D *ᵥ ω.2)
    with hyf
  set ex : (Fin nP → ℝ) × (Fin nQ → ℝ) → (Fin e → ℝ) := fun ω => E *ᵥ ω.1 + F *ᵥ ω.2 with hex
  set P : Set ((Fin nP → ℝ) × (Fin nQ → ℝ)) :=
    {ω | (∀ k, 0 ≤ (G *ᵥ yf ω) k) ∧ ∀ i, ex ω i ≤ ee i} with hP
  have hyaff : ∀ (ω ω' : (Fin nP → ℝ) × (Fin nQ → ℝ)) (a b : ℝ), a + b = 1 →
      yf (a • ω + b • ω') = a • yf ω + b • yf ω' := by
    intro ω ω' a b hab
    simp only [hyf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
      mulVec_smul]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : c i = a * c i + b * c i := by rw [← add_mul, hab, one_mul]
    linarith
  have hexlin : ∀ (ω ω' : (Fin nP → ℝ) × (Fin nQ → ℝ)) (a b : ℝ),
      ex (a • ω + b • ω') = a • ex ω + b • ex ω' := by
    intro ω ω' a b
    simp only [hex, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
      mulVec_smul, smul_add]
    abel
  set q : (Fin nP → ℝ) × (Fin nQ → ℝ) → ℝ := fun ω => a ⬝ᵥ ω.1 + b ⬝ᵥ ω.2 with hq
  have hconvS : Convex ℝ ((fun ω => (yf ω, q ω)) '' P) := by
    rintro _ ⟨ω, hω, rfl⟩ _ ⟨ω', hω', rfl⟩ a' b' ha hb hab
    refine ⟨a' • ω + b' • ω', ⟨?_, ?_⟩, ?_⟩
    · intro k
      rw [hyaff ω ω' a' b' hab, mulVec_add, mulVec_smul, mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hω.1 k)) (mul_nonneg hb (hω'.1 k))
    · intro i
      rw [hexlin]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1 := mul_le_mul_of_nonneg_left (hω.2 i) ha
      have h2 := mul_le_mul_of_nonneg_left (hω'.2 i) hb
      have : ee i = a' * ee i + b' * ee i := by rw [← add_mul, hab, one_mul]
      linarith
    · simp only [hyaff ω ω' a' b' hab, hq, Prod.smul_mk, Prod.mk_add_mk, Prod.fst_add,
        Prod.smul_fst, Prod.snd_add, Prod.smul_snd, dotProduct_add, dotProduct_smul, smul_eq_mul]
      ring_nf
  have hstP : ∀ ω ∈ P, yf ω ∈ Kn → q ω ≤ δ := fun ω hω hK => hst ω hω.1 hK hω.2
  obtain ⟨ψn, hψnK, hψnP⟩ := DRUQConicAux.step1 P yf q hconvS Kn hKconv hKsm
    ω0 ⟨hω0p, hω0e⟩ hω0n δ hstP
  -- LP part
  set zx : (Fin (nP + nQ) → ℝ) → (Fin nP → ℝ) := fun x a => x (Fin.castAdd nQ a) with hzx
  set ux : (Fin (nP + nQ) → ℝ) → (Fin nQ → ℝ) := fun x b => x (Fin.natAdd nP b) with hux
  set R1 : Fin r → Fin (nP + nQ) → ℝ :=
    fun i => Fin.append (fun a => -((G * C) i a)) (fun b => -((G * D) i b)) with hR1
  set R2 : Fin e → Fin (nP + nQ) → ℝ :=
    fun i => Fin.append (fun a => -(E i a)) (fun b => -(F i b)) with hR2
  set M : Matrix (Fin (r + e)) (Fin (nP + nQ)) ℝ := Matrix.of (Fin.append R1 R2) with hM
  set bb : Fin (r + e) → ℝ := Fin.append (-(G *ᵥ c)) (-ee) with hbb
  set cc : Fin (nP + nQ) → ℝ :=
    Fin.append (fun a' => -(a - Cᵀ *ᵥ ψn) a') (fun b' => -(b - Dᵀ *ᵥ ψn) b') with hcc
  have hR1x : ∀ x i, ∑ k, R1 i k * x k = -(((G * C) *ᵥ zx x) i + ((G * D) *ᵥ ux x) i) := by
    intro x i
    simp only [mulVec, dotProduct, hR1, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, hzx, hux]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]
  have hR2x : ∀ x i, ∑ k, R2 i k * x k = -((E *ᵥ zx x) i + (F *ᵥ ux x) i) := by
    intro x i
    simp only [mulVec, dotProduct, hR2, Fin.sum_univ_add, Fin.append_left,
      Fin.append_right, hzx, hux]
    simp only [neg_mul, Finset.sum_neg_distrib, neg_add]
  have hccx : ∀ x, ∑ k, cc k * x k = -((a - Cᵀ *ᵥ ψn) ⬝ᵥ zx x) - (b - Dᵀ *ᵥ ψn) ⬝ᵥ ux x := by
    intro x
    simp only [hcc, Fin.sum_univ_add, Fin.append_left, Fin.append_right, dotProduct, hzx, hux,
      neg_mul, Finset.sum_neg_distrib]
    ring
  have hpoly : ∀ x, x ∈ LinearOptimization.polyhedron M bb ↔ (zx x, ux x) ∈ P := by
    intro x
    simp only [LinearOptimization.polyhedron, Set.mem_ofPred_eq, hP, Pi.le_def]
    rw [Fin.forall_fin_add]
    apply and_congr
    · apply forall_congr'
      intro i
      have he := hR1x x i
      rw [← mulVec_mulVec, ← mulVec_mulVec] at he
      have hMi : (M *ᵥ x) (Fin.castAdd e i) = ∑ k, R1 i k * x k := by
        simp only [mulVec, dotProduct, hM, Matrix.of_apply, Fin.append_left]
      have hbi : bb (Fin.castAdd e i) = -(G *ᵥ c) i := by simp only [hbb, Fin.append_left, Pi.neg_apply]
      show bb (Fin.castAdd e i) ≤ (M *ᵥ x) (Fin.castAdd e i) ↔ _
      rw [hMi, hbi, he]
      simp only [hyf, mulVec_sub, mulVec_add, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      constructor <;> intro h <;> linarith
    · apply forall_congr'
      intro i
      have he := hR2x x i
      have hMi : (M *ᵥ x) (Fin.natAdd r i) = ∑ k, R2 i k * x k := by
        simp only [mulVec, dotProduct, hM, Matrix.of_apply, Fin.append_right]
      have hbi : bb (Fin.natAdd r i) = -ee i := by simp only [hbb, Fin.append_right, Pi.neg_apply]
      show bb (Fin.natAdd r i) ≤ (M *ᵥ x) (Fin.natAdd r i) ↔ _
      rw [hMi, hbi, he]
      simp only [hex, Pi.add_apply]
      constructor <;> intro h <;> linarith
  have hfeas : (LinearOptimization.polyhedron M bb).Nonempty := by
    refine ⟨Fin.append ω0.1 ω0.2, (hpoly _).mpr ?_⟩
    have e1 : zx (Fin.append ω0.1 ω0.2) = ω0.1 := by
      funext a; simp [hzx, Fin.append_left]
    have e2 : ux (Fin.append ω0.1 ω0.2) = ω0.2 := by
      funext b; simp [hux, Fin.append_right]
    rw [e1, e2]; exact ⟨hω0p, hω0e⟩
  have hTr : ∀ {k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (z : Fin k → ℝ),
      (A *ᵥ z) ⬝ᵥ ψn = (Aᵀ *ᵥ ψn) ⬝ᵥ z := by
    intro k A z
    rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose]
  have hbdd' : ∀ x ∈ LinearOptimization.polyhedron M bb, ψn ⬝ᵥ c - δ ≤ ∑ k, cc k * x k := by
    intro x hx
    have h := hψnP (zx x, ux x) ((hpoly x).mp hx)
    rw [hccx]
    simp only [hyf, hq] at h
    rw [sub_dotProduct, add_dotProduct, hTr, hTr] at h
    rw [sub_dotProduct, sub_dotProduct]
    have := dotProduct_comm c ψn
    linarith
  have hbdd : ∃ v : ℝ, ∀ x ∈ LinearOptimization.polyhedron M bb, v ≤ ∑ k, cc k * x k :=
    ⟨_, hbdd'⟩
  obtain ⟨xs, y, hxs, hy0, hyM, hval, -⟩ := SmaleNinth.lp_strong_duality M bb cc hfeas hbdd
  set y1 : Fin r → ℝ := fun i => y (Fin.castAdd e i) with hy1
  set y2 : Fin e → ℝ := fun i => y (Fin.natAdd r i) with hy2
  set w := Gᵀ *ᵥ y1 with hw
  have hsplit : ∀ k, ∑ i, y i * M i k = ∑ i, y1 i * R1 i k + ∑ i, y2 i * R2 i k := by
    intro k
    simp only [hM, Matrix.of_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right, hy1, hy2]
  have hCw : Cᵀ *ᵥ w + Eᵀ *ᵥ y2 = a - Cᵀ *ᵥ ψn := by
    funext a'
    have h := hyM (Fin.castAdd nQ a')
    rw [hsplit] at h
    simp only [hR1, hR2, hcc, Fin.append_left, mul_neg, Finset.sum_neg_distrib] at h
    rw [hw, mulVec_mulVec, ← transpose_mul, Pi.add_apply]
    have e1 : ((G * C)ᵀ *ᵥ y1) a' = ∑ i, y1 i * (G * C) i a' := by
      simp only [mulVec, dotProduct, transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have e2 : (Eᵀ *ᵥ y2) a' = ∑ i, y2 i * E i a' := by
      simp only [mulVec, dotProduct, transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e1, e2]; linarith
  have hDw : Dᵀ *ᵥ w + Fᵀ *ᵥ y2 = b - Dᵀ *ᵥ ψn := by
    funext b'
    have h := hyM (Fin.natAdd nP b')
    rw [hsplit] at h
    simp only [hR1, hR2, hcc, Fin.append_right, mul_neg, Finset.sum_neg_distrib] at h
    rw [hw, mulVec_mulVec, ← transpose_mul, Pi.add_apply]
    have e1 : ((G * D)ᵀ *ᵥ y1) b' = ∑ i, y1 i * (G * D) i b' := by
      simp only [mulVec, dotProduct, transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have e2 : (Fᵀ *ᵥ y2) b' = ∑ i, y2 i * F i b' := by
      simp only [mulVec, dotProduct, transpose_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e1, e2]; linarith
  have hcw : c ⬝ᵥ w + ee ⬝ᵥ y2 ≤ δ - ψn ⬝ᵥ c := by
    have h1 := hbdd' xs hxs
    rw [hval] at h1
    have e : c ⬝ᵥ w + ee ⬝ᵥ y2 = -∑ i, y i * bb i := by
      rw [hw, dotProduct_mulVec, vecMul_transpose, hbb, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, dotProduct, Pi.neg_apply, mul_neg,
        Finset.sum_neg_distrib, neg_neg, neg_add, hy1, hy2]
      congr 1
      · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      · exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [e]; linarith
  refine ⟨ψn + w, y2, ?_, fun i => hy0 (Fin.natAdd r i), ?_, ?_, ?_⟩
  · intro x hxp hxn
    rw [dotProduct_add]
    apply add_nonneg (hψnK x hxn)
    rw [hw, dotProduct_mulVec, vecMul_transpose]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (hxp i) (hy0 _))
  · rw [mulVec_add, add_assoc, hCw]; abel
  · rw [mulVec_add, add_assoc, hDw]; abel
  · rw [dotProduct_add, add_assoc]; have := dotProduct_comm c ψn; linarith

open MeasureTheory in
/-- Moment-problem duality with dual attainment, via separation (Markov case). -/
theorem DRUQConicAux.moment_dual {nP nQ nK : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hCcl : IsClosed (amb.conf 0)) (hS : SlaterI1 amb)
    (Ev : Set ((Fin nP → ℝ) × (Fin nQ → ℝ))) (hEv : MeasurableSet Ev) (p0 : ℝ)
    (hcc : ∀ μ ∈ paperAmbiguitySet amb, p0 ≤ μ.real Ev) :
    ∃ (γ : Fin nK → ℝ) (β : ℝ),
      (∀ ω ∈ amb.conf 0, γ ⬝ᵥ (amb.A *ᵥ ω.1 + amb.B *ᵥ ω.2) + β ≤ Ev.indicator 1 ω) ∧
      p0 ≤ amb.b ⬝ᵥ γ + β := by
  set g : ((Fin nP → ℝ) × (Fin nQ → ℝ)) → (Fin nK → ℝ) := fun ω => amb.A *ᵥ ω.1 + amb.B *ᵥ ω.2 with hg
  set C1 := amb.conf 0 with hC1
  have hC1m : MeasurableSet C1 := hCcl.measurableSet
  have hgc : Continuous g :=
    (Continuous.matrix_mulVec continuous_const continuous_fst).add
      (Continuous.matrix_mulVec continuous_const continuous_snd)
  set W : Set ((Fin nK → ℝ) × ℝ) := {x | ∃ μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ)), IsProbabilityMeasure μ ∧
      μ C1ᶜ = 0 ∧ Integrable g μ ∧ ∫ ω, g ω ∂μ = x.1 ∧ μ.real Ev ≤ x.2} with hW
  -- members of `W` give members of the ambiguity set
  have hmemA : ∀ μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ)), IsProbabilityMeasure μ → μ C1ᶜ = 0 → Integrable g μ →
      ∫ ω, g ω ∂μ = amb.b → μ ∈ paperAmbiguitySet amb := by
    intro μ hP hc hi hb
    refine ⟨hP, hi, hb, ?_⟩
    intro i
    obtain rfl : i = 0 := Fin.fin_one_eq_zero i
    rw [hM.1, hM.2]
    have h1 : μ C1 = 1 := (prob_compl_eq_zero_iff hC1m).mp hc
    have : μ.real (amb.conf 0) = 1 := by
      rw [measureReal_def, ← hC1, h1, ENNReal.toReal_one]
    rw [this]; exact ⟨le_rfl, le_rfl⟩
  -- Dirac measures
  have hdirac : ∀ ω ∈ C1, (g ω, Ev.indicator 1 ω) ∈ W := by
    intro ω hω
    refine ⟨Measure.dirac ω, inferInstance, ?_, ?_, ?_, ?_⟩
    · rw [Measure.dirac_apply' _ hC1m.compl]
      simp [hω]
    · exact integrable_dirac enorm_lt_top
    · simp only
      rw [integral_dirac]
    · simp only
      rw [measureReal_def, Measure.dirac_apply' _ hEv]
      by_cases h : ω ∈ Ev <;> simp [h]
  have hup : ∀ x ∈ W, ∀ p, x.2 ≤ p → (x.1, p) ∈ W := by
    rintro x ⟨μ, h1, h2, h3, h4, h5⟩ p hp
    exact ⟨μ, h1, h2, h3, h4, h5.trans hp⟩
  -- convexity
  have hWconv : Convex ℝ W := by
    rintro x ⟨μ1, hP1, hc1, hi1, hb1, he1⟩ x' ⟨μ2, hP2, hc2, hi2, hb2, he2⟩ a b ha hb hab
    refine ⟨ENNReal.ofReal a • μ1 + ENNReal.ofReal b • μ2, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
    · simp [Measure.add_apply, Measure.smul_apply, hc1, hc2]
    · exact (hi1.smul_measure ENNReal.ofReal_ne_top).add_measure
        (hi2.smul_measure ENNReal.ofReal_ne_top)
    · rw [integral_add_measure (hi1.smul_measure ENNReal.ofReal_ne_top)
        (hi2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
        ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb, hb1, hb2]
      rfl
    · have e : (ENNReal.ofReal a • μ1 + ENNReal.ofReal b • μ2).real Ev =
          a * μ1.real Ev + b * μ2.real Ev := by
        simp only [measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
          ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
          ENNReal.toReal_ofReal hb]
      rw [e]
      show a * μ1.real Ev + b * μ2.real Ev ≤ a * x.2 + b * x'.2
      nlinarith [mul_le_mul_of_nonneg_left he1 ha, mul_le_mul_of_nonneg_left he2 hb]
  -- an open subset of `W`
  set U : Set ((Fin nK → ℝ) × ℝ) := interior (g '' C1) ×ˢ Set.Ioi 1 with hU
  have hUW : U ⊆ W := by
    rintro ⟨w, p⟩ ⟨hw, hp⟩
    obtain ⟨ω, hω, rfl⟩ := interior_subset hw
    apply hup _ (hdirac ω hω) p
    simp only [Set.mem_Ioi] at hp
    show Ev.indicator 1 ω ≤ p
    by_cases h : ω ∈ Ev <;> simp [h] <;> linarith
  have hUopen : IsOpen U := isOpen_interior.prod isOpen_Ioi
  have hbU : (amb.b, (2 : ℝ)) ∈ U := ⟨hS, by norm_num⟩
  have hintne : (interior W).Nonempty := ⟨_, interior_maximal hUW hUopen hbU⟩
  -- the point `(b, p0)` is not interior
  have hnot : (amb.b, p0) ∉ interior W := by
    intro hx
    have ho : IsOpen {p : ℝ | (amb.b, p) ∈ interior W} :=
      isOpen_interior.preimage (Continuous.prodMk continuous_const continuous_id)
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho p0 hx
    have hmem : p0 - δ / 2 ∈ Metric.ball p0 δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      rw [show p0 - δ / 2 - p0 = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
      linarith
    obtain ⟨μ, h1, h2, h3, h4, h5⟩ := interior_subset (hball hmem)
    have := hcc μ (hmemA μ h1 h2 h3 h4)
    simp only at h5
    linarith
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hWconv.interior isOpen_interior hnot
  have hWcl : W ⊆ closure (interior W) := by
    rw [hWconv.closure_interior_eq_closure_of_nonempty_interior hintne]
    exact subset_closure
  have hfW : ∀ x ∈ W, f x ≤ f (amb.b, p0) := by
    intro x hx
    have hcl : closure (interior W) ⊆ {y | f y ≤ f (amb.b, p0)} :=
      closure_minimal (fun y hy => (hf y hy).le) (isClosed_le f.continuous continuous_const)
    exact hcl (hWcl hx)
  have hfs : ∀ (w : Fin nK → ℝ) (p : ℝ), f (w, p) = f (w, 0) + p * f (0, 1) := by
    intro w p
    have : ((w, p) : (Fin nK → ℝ) × ℝ) = (w, 0) + p • ((0 : Fin nK → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set θ := f (0, 1) with hθ
  obtain ⟨ω0, hω0, hω0b⟩ := interior_subset hS
  -- θ ≤ 0
  have hθle : θ ≤ 0 := by
    by_contra hpos
    rw [not_le] at hpos
    set p := max 1 ((|f (amb.b, p0) - f (g ω0, 0)| + 1) / θ) with hp
    have h1 := hfW _ (hup _ (hdirac ω0 hω0) p (by
      show Ev.indicator 1 ω0 ≤ p
      have : Ev.indicator (1 : ((Fin nP → ℝ) × (Fin nQ → ℝ)) → ℝ) ω0 ≤ 1 := by
        by_cases h : ω0 ∈ Ev <;> simp [h]
      exact this.trans (le_max_left _ _)))
    rw [hfs] at h1
    simp only at h1
    have h2 : (|f (amb.b, p0) - f (g ω0, 0)| + 1) / θ ≤ p := le_max_right _ _
    have h3 := mul_le_mul_of_nonneg_right h2 hpos.le
    rw [div_mul_cancel₀ _ hpos.ne'] at h3
    have := le_abs_self (f (amb.b, p0) - f (g ω0, 0))
    linarith
  -- represent `w ↦ f (w, 0)` by a vector
  set g' : (Fin nK → ℝ) →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ (Fin nK → ℝ) ℝ) with hg'
  have hg'apply : ∀ w, g' w = f (w, 0) := fun w => rfl
  set v : Fin nK → ℝ := fun i => g' (fun j => if i = j then 1 else 0) with hv
  have hgv : ∀ w, f (w, 0) = w ⬝ᵥ v := by
    intro w
    rw [← hg'apply]
    have := (g' : (Fin nK → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ w
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    simp [dotProduct, hv, smul_eq_mul]
  -- θ < 0
  have hθlt : θ < 0 := by
    rcases hθle.lt_or_eq with h | h
    · exact h
    · exfalso
      -- then `w ↦ f (w, 0)` is maximized at `b` over a neighbourhood, hence zero
      have hmax : ∀ w ∈ g '' C1, f (w, 0) ≤ f (amb.b, 0) := by
        rintro _ ⟨ω, hω, rfl⟩
        have h1 := hfW _ (hdirac ω hω)
        rw [hfs, hfs (amb.b) p0, h] at h1
        simpa using h1
      have hzero : ∀ u : Fin nK → ℝ, f (u, 0) = 0 := by
        intro u
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior amb.b hS
        set κ := r / (2 * (‖u‖ + 1)) with hκ
        have hκ0 : 0 < κ := div_pos hr (by positivity)
        have hκu : ‖κ • u‖ < r := by
          rw [norm_smul, Real.norm_of_nonneg hκ0.le, hκ]
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [norm_nonneg u]
        have hp : amb.b + κ • u ∈ g '' C1 := interior_subset (hball (by
          rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hκu))
        have hm : amb.b - κ • u ∈ g '' C1 := interior_subset (hball (by
          rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact hκu))
        have e1 := hmax _ hp
        have e2 := hmax _ hm
        rw [hgv, hgv, add_dotProduct, smul_dotProduct, smul_eq_mul] at e1
        rw [hgv, hgv, sub_dotProduct, smul_dotProduct, smul_eq_mul] at e2
        rw [hgv]
        have h3 : κ * (u ⬝ᵥ v) = 0 := by linarith
        rcases mul_eq_zero.mp h3 with h4 | h4
        · linarith
        · exact h4
      obtain ⟨x, hx⟩ := hintne
      have := hf x hx
      rw [hfs, hfs (amb.b) p0, h, hzero, hzero] at this
      simp at this
  refine ⟨-θ⁻¹ • v, p0 - amb.b ⬝ᵥ (-θ⁻¹ • v), ?_, by linarith⟩
  intro ω hω
  have h1 := hfW _ (hdirac ω hω)
  rw [hfs, hfs (amb.b) p0, hgv, hgv] at h1
  try simp only at h1
  have hw : θ⁻¹ < 0 := inv_lt_zero.mpr hθlt
  have hθ0 : θ ≠ 0 := hθlt.ne
  have h2 := mul_le_mul_of_nonpos_left h1 hw.le
  have e1 : θ⁻¹ * (g ω ⬝ᵥ v + Ev.indicator 1 ω * θ) = θ⁻¹ * (g ω ⬝ᵥ v) + Ev.indicator 1 ω := by
    rw [mul_add, mul_comm (Ev.indicator 1 ω) θ, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul]
  have e2 : θ⁻¹ * (amb.b ⬝ᵥ v + p0 * θ) = θ⁻¹ * (amb.b ⬝ᵥ v) + p0 := by
    rw [mul_add, mul_comm p0 θ, ← mul_assoc, inv_mul_cancel₀ hθ0, one_mul]
  rw [e1, e2] at h2
  simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [dotProduct_comm v]
  show -θ⁻¹ * (g ω ⬝ᵥ v) + (p0 - -θ⁻¹ * (amb.b ⬝ᵥ v)) ≤ Ev.indicator 1 ω
  linarith

theorem DRUQConicAux.sec5_core {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0))
    (hE : EssStrictFeas (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0)) (hS : SlaterI1 amb)
    (S : Matrix (Fin nJ) (Fin nP) ℝ) (t : Fin nJ → ℝ) (p0 : ℝ)
    (hcc : ∀ μ ∈ paperAmbiguitySet amb, p0 ≤ μ.real {ω | S *ᵥ ω.1 ≤ t}) :
      ∃ (γ : Fin nK → ℝ) (lam kap : ℝ) (φ : Fin (amb.L 0) → ℝ) (τ : Fin nJ → ℝ)
        (ψ : Fin nJ → Fin (amb.L 0) → ℝ),
        UQFeasible amb S t γ lam kap φ τ ψ ∧ p0 ≤ uqObjective amb γ lam kap := by
  · obtain ⟨r, G, Kn, hKc, hKconv, hKsm, hKeq, ω0, hω0p, hω0n⟩ := hE
    set yf : (Fin nP → ℝ) × (Fin nQ → ℝ) → (Fin (amb.L 0) → ℝ) :=
      fun ω => amb.c 0 - (amb.C 0 *ᵥ ω.1 + amb.D 0 *ᵥ ω.2) with hyf
    have hcont : Continuous yf := by
      apply Continuous.sub continuous_const
      apply Continuous.add
      · exact (Continuous.matrix_mulVec continuous_const continuous_fst)
      · exact (Continuous.matrix_mulVec continuous_const continuous_snd)
    have hCcl : IsClosed (amb.conf 0) := hK.1.preimage hcont
    have hEcl : IsClosed {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | S *ᵥ ω.1 ≤ t} :=
      isClosed_le (Continuous.matrix_mulVec continuous_const continuous_fst) continuous_const
    obtain ⟨γ, β, hγβ, hobj⟩ :=
      DRUQConicAux.moment_dual amb hM hCcl hS _ hEcl.measurableSet p0 hcc
    have hid : ∀ ω : (Fin nP → ℝ) × (Fin nQ → ℝ), γ ⬝ᵥ (amb.A *ᵥ ω.1 + amb.B *ᵥ ω.2) =
        (amb.Aᵀ *ᵥ γ) ⬝ᵥ ω.1 + (amb.Bᵀ *ᵥ γ) ⬝ᵥ ω.2 := by
      intro ω
      rw [dotProduct_add, dotProduct_mulVec, dotProduct_mulVec, ← mulVec_transpose,
        ← mulVec_transpose]
    have hconfK : ∀ ω, ω ∈ amb.conf 0 ↔ (∀ k, 0 ≤ (G *ᵥ yf ω) k) ∧ yf ω ∈ Kn := by
      intro ω
      show yf ω ∈ amb.K 0 ↔ _
      rw [hKeq]; rfl
    have hdualK : ∀ θ : Fin (amb.L 0) → ℝ,
        (∀ x, (∀ k, 0 ≤ (G *ᵥ x) k) → x ∈ Kn → 0 ≤ x ⬝ᵥ θ) → θ ∈ dualCone (amb.K 0) := by
      intro θ h x hx
      rw [hKeq] at hx
      exact h x hx.1 hx.2
    have hyaff : ∀ (ω ω' : (Fin nP → ℝ) × (Fin nQ → ℝ)) (a b : ℝ), a + b = 1 →
        yf (a • ω + b • ω') = a • yf ω + b • yf ω' := by
      intro ω ω' a b hab
      simp only [hyf, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, mulVec_add,
        mulVec_smul]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : amb.c 0 i = a * amb.c 0 i + b * amb.c 0 i := by rw [← add_mul, hab, one_mul]
      linarith
    have hCconv : ∀ ω ∈ amb.conf 0, ∀ ω' ∈ amb.conf 0, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        a • ω + b • ω' ∈ amb.conf 0 := by
      intro ω hω ω' hω' a b ha hb hab
      rw [hconfK] at hω hω' ⊢
      rw [hyaff ω ω' a b hab]
      refine ⟨fun k => ?_, hKconv hω.2 hω'.2 ha hb hab⟩
      rw [mulVec_add, mulVec_smul, mulVec_smul]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hω.1 k)) (mul_nonneg hb (hω'.1 k))
    have hind1 : ∀ ω, ({ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | S *ᵥ ω.1 ≤ t}.indicator 1 ω : ℝ) ≤ 1 := by
      intro ω
      by_cases h : ω ∈ {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | S *ᵥ ω.1 ≤ t} <;> simp [h]
    -- the multiplier `φ`
    obtain ⟨φ, ν0, hφK, -, hφC, hφD, hφc⟩ := DRUQConicAux.conic_gen (amb.C 0) (amb.D 0)
      (amb.c 0) G Kn hKconv hKsm (0 : Matrix (Fin 0) (Fin nP) ℝ) (0 : Matrix (Fin 0) (Fin nQ) ℝ)
      0 ω0 hω0p hω0n (fun i => Fin.elim0 i) (amb.Aᵀ *ᵥ γ) (amb.Bᵀ *ᵥ γ) (1 - β) (by
        intro ω h1 h2 _
        have := hγβ ω ((hconfK ω).2 ⟨h1, h2⟩)
        rw [hid] at this
        have := hind1 ω
        linarith)
    simp only [transpose_zero, zero_mulVec, add_zero, zero_dotProduct] at hφC hφD hφc
    -- the multipliers `ψ j`, `τ j`
    have hj : ∀ j, ∃ (τj : ℝ) (ψj : Fin (amb.L 0) → ℝ), j ∈ violIdx amb S t →
        (0 ≤ τj ∧ ψj ∈ dualCone (amb.K 0) ∧ (β + amb.c 0 ⬝ᵥ ψj - τj * t j ≤ 0) ∧
          amb.Aᵀ *ᵥ γ + τj • S j = (amb.C 0)ᵀ *ᵥ ψj ∧ amb.Bᵀ *ᵥ γ = (amb.D 0)ᵀ *ᵥ ψj) := by
      intro j
      by_cases hjL : j ∈ violIdx amb S t
      swap
      · exact ⟨0, 0, fun h => absurd h hjL⟩
      obtain ⟨ω1, hω1, hω1t⟩ := by
        simpa only [violIdx, Finset.mem_filter, Finset.mem_univ, true_and] using hjL
      have hSz : ∀ z : Fin nP → ℝ, (S *ᵥ z) j = S j ⬝ᵥ z := fun z => rfl
      -- `h ≤ 0` on `C₁ ∩ {s_jᵀ z ≥ t_j}`
      set hh : (Fin nP → ℝ) × (Fin nQ → ℝ) → ℝ :=
        fun ω => (amb.Aᵀ *ᵥ γ) ⬝ᵥ ω.1 + (amb.Bᵀ *ᵥ γ) ⬝ᵥ ω.2 + β with hhh
      have hstrict : ∀ ω ∈ amb.conf 0, t j < S j ⬝ᵥ ω.1 → hh ω ≤ 0 := by
        intro ω hω hlt
        have h1 := hγβ ω hω
        have hnot : ω ∉ {ω : (Fin nP → ℝ) × (Fin nQ → ℝ) | S *ᵥ ω.1 ≤ t} := by
          intro hin
          have := hin j
          rw [hSz] at this
          linarith
        rw [Set.indicator_of_notMem hnot, hid] at h1
        exact h1
      have hhaff : ∀ (ω ω' : (Fin nP → ℝ) × (Fin nQ → ℝ)) (a b : ℝ), a + b = 1 →
          hh (a • ω + b • ω') = a * hh ω + b * hh ω' := by
        intro ω ω' a b hab
        simp only [hhh, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          dotProduct_add, dotProduct_smul, smul_eq_mul]
        have : β = a * β + b * β := by rw [← add_mul, hab, one_mul]
        linarith
      have hweak : ∀ ω ∈ amb.conf 0, t j ≤ S j ⬝ᵥ ω.1 → hh ω ≤ 0 := by
        intro ω hω hle
        by_contra hpos
        rw [not_le] at hpos
        have H1 := hstrict ω1 hω1 hω1t
        set l := hh ω / (2 * (hh ω - hh ω1)) with hl
        have hden : 0 < 2 * (hh ω - hh ω1) := by linarith
        have hl0 : 0 < l := div_pos hpos hden
        have hl1 : l ≤ 1 / 2 := by
          rw [hl, div_le_iff₀ hden]; linarith
        have hmem := hCconv ω hω ω1 hω1 (1 - l) l (by linarith) hl0.le (by ring)
        have hlt : t j < S j ⬝ᵥ ((1 - l) • ω + l • ω1).1 := by
          simp only [Prod.fst_add, Prod.smul_fst, dotProduct_add, dotProduct_smul, smul_eq_mul]
          nlinarith
        have h3 := hstrict _ hmem hlt
        rw [hhaff ω ω1 (1 - l) l (by ring)] at h3
        have e : l * (2 * (hh ω - hh ω1)) = hh ω := by
          rw [hl, div_mul_cancel₀ _ hden.ne']
        nlinarith
      -- strictly feasible point inside the half-space
      set d := S j ⬝ᵥ ω1.1 - t j with hd
      have hd0 : 0 < d := by linarith
      set Δ := S j ⬝ᵥ ω1.1 - S j ⬝ᵥ ω0.1 with hΔ
      set l := d / (2 * (|Δ| + d)) with hl
      have hden : 0 < 2 * (|Δ| + d) := by positivity
      have hl0 : 0 < l := div_pos hd0 hden
      have hl1 : l ≤ 1 / 2 := by
        rw [hl, div_le_iff₀ hden]; nlinarith [abs_nonneg Δ]
      have hlΔ : l * |Δ| ≤ d / 2 := by
        rw [hl, div_mul_eq_mul_div, div_le_iff₀ hden]; nlinarith [abs_nonneg Δ]
      set ω0' := (1 - l) • ω1 + l • ω0 with hω0'
      have hω1K := (hconfK ω1).1 hω1
      have hy0' : yf ω0' = l • yf ω0 + (1 - l) • yf ω1 := by
        rw [hω0', hyaff ω1 ω0 (1 - l) l (by ring)]; exact add_comm _ _
      have hω0'p : ∀ k, 0 ≤ (G *ᵥ yf ω0') k := by
        intro k
        rw [hy0', mulVec_add, mulVec_smul, mulVec_smul]
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        exact add_nonneg (mul_nonneg hl0.le (hω0p k)) (mul_nonneg (by linarith) (hω1K.1 k))
      have hω0'n : yf ω0' ∈ interior Kn := by
        rw [hy0']
        exact hKconv.combo_interior_closure_mem_interior hω0n (subset_closure hω1K.2) hl0
          (by linarith) (by ring)
      have hω0't : t j ≤ S j ⬝ᵥ ω0'.1 := by
        simp only [hω0', Prod.fst_add, Prod.smul_fst, dotProduct_add, dotProduct_smul,
          smul_eq_mul]
        have : -(l * |Δ|) ≤ -(l * Δ) := by
          have := le_abs_self Δ
          nlinarith
        nlinarith
      set Er : Matrix (Fin 1) (Fin nP) ℝ := Matrix.of fun _ => -S j with hEr
      have hEz : ∀ z : Fin nP → ℝ, (Er *ᵥ z) 0 = -(S j ⬝ᵥ z) := by
        intro z
        simp [hEr, mulVec, dotProduct, Finset.sum_neg_distrib]
      obtain ⟨ψj, ν, hψK, hν0, hψC, hψD, hψc⟩ := DRUQConicAux.conic_gen (amb.C 0) (amb.D 0)
        (amb.c 0) G Kn hKconv hKsm Er (0 : Matrix (Fin 1) (Fin nQ) ℝ) (fun _ => -t j) ω0'
        hω0'p hω0'n (by
          intro i
          obtain rfl : i = 0 := Fin.fin_one_eq_zero i
          rw [zero_mulVec, add_zero, hEz]; linarith)
        (amb.Aᵀ *ᵥ γ) (amb.Bᵀ *ᵥ γ) (-β) (by
          intro ω h1 h2 h3
          have h4 := h3 0
          rw [zero_mulVec, add_zero, hEz] at h4
          have := hweak ω ((hconfK ω).2 ⟨h1, h2⟩) (by linarith)
          simp only [hhh] at this
          linarith)
      have hEν : Erᵀ *ᵥ ν = -(ν 0 • S j) := by
        funext a
        simp [hEr, mulVec, dotProduct, transpose_apply, mul_comm]
      refine ⟨ν 0, ψj, fun _ => ⟨hν0 0, hdualK ψj hψK, ?_, ?_, ?_⟩⟩
      · have : (fun _ => -t j : Fin 1 → ℝ) ⬝ᵥ ν = -(ν 0 * t j) := by
          simp [dotProduct, mul_comm]
        rw [this] at hψc
        linarith
      · rw [← hψC, hEν]; abel
      · rw [← hψD]; simp
    choose τ ψ hτψ using hj
    refine ⟨γ, max β 0, max (-β) 0, φ, τ, ψ, ⟨le_max_right _ _, le_max_right _ _,
      hdualK φ hφK, ?_, hφC.symm, hφD.symm, ?_⟩, ?_⟩
    · rw [max_zero_sub_max_neg_zero_eq_self]; linarith
    · intro j hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := hτψ j hj
      refine ⟨h1, h2, ?_, h4, h5⟩
      rw [max_zero_sub_max_neg_zero_eq_self]; exact h3
    · simp only [uqObjective, hM.1, hM.2, one_mul]
      have := max_zero_sub_max_neg_zero_eq_self β
      linarith

theorem solution {nP nQ nK nJ : ℕ} (amb : AmbData nP nQ nK 0) (hM : IsMarkov amb)
    (hK : IsProperCone (amb.K 0))
    (hE : EssStrictFeas (amb.C 0) (amb.D 0) (amb.c 0) (amb.K 0)) (hS : SlaterI1 amb)
    (S : Matrix (Fin nJ) (Fin nP) ℝ) (t : Fin nJ → ℝ) :
    ∃ v : ℝ,
      IsGLB {p : ℝ | ∃ μ ∈ paperAmbiguitySet amb, p = μ.real {ω | S *ᵥ ω.1 ≤ t}} v ∧
      IsLUB {o : ℝ | ∃ (γ : Fin nK → ℝ) (lam kap : ℝ) (φ : Fin (amb.L 0) → ℝ)
          (τ : Fin nJ → ℝ) (ψ : Fin nJ → Fin (amb.L 0) → ℝ),
          UQFeasible amb S t γ lam kap φ τ ψ ∧ o = uqObjective amb γ lam kap} v := by
  set Pr := {p : ℝ | ∃ μ ∈ paperAmbiguitySet amb, p = μ.real {ω | S *ᵥ ω.1 ≤ t}} with hPr
  -- a Dirac measure lies in the ambiguity set
  have hcont : Continuous (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) =>
      amb.c 0 - (amb.C 0 *ᵥ ω.1 + amb.D 0 *ᵥ ω.2)) := by
    apply Continuous.sub continuous_const
    apply Continuous.add
    · exact (Continuous.matrix_mulVec continuous_const continuous_fst)
    · exact (Continuous.matrix_mulVec continuous_const continuous_snd)
  have hC1m : MeasurableSet (amb.conf 0) := (hK.1.preimage hcont).measurableSet
  obtain ⟨ω0, hω0, hω0b⟩ := interior_subset hS
  have hdirac : MeasureTheory.Measure.dirac ω0 ∈ paperAmbiguitySet amb := by
    refine ⟨inferInstance, MeasureTheory.integrable_dirac enorm_lt_top, ?_, ?_⟩
    · rw [MeasureTheory.integral_dirac]; exact hω0b
    · intro i
      obtain rfl : i = 0 := Fin.fin_one_eq_zero i
      rw [hM.1, hM.2, MeasureTheory.measureReal_def,
        MeasureTheory.Measure.dirac_apply' _ hC1m]
      simp [hω0]
  have hne : Pr.Nonempty := ⟨_, _, hdirac, rfl⟩
  have hbdd : BddBelow Pr := ⟨0, by rintro p ⟨μ, -, rfl⟩; exact MeasureTheory.measureReal_nonneg⟩
  refine ⟨sInf Pr, isGLB_csInf hne hbdd, ?_, ?_⟩
  · rintro o ⟨γ, lam, kap, φ, τ, ψ, hfeas, rfl⟩
    apply le_csInf hne
    rintro p ⟨μ, hμ, rfl⟩
    exact theorem_3_if amb hM hK S t γ lam kap φ τ ψ hfeas μ hμ
  · intro u hu
    obtain ⟨γ, lam, kap, φ, τ, ψ, hfeas, hobj⟩ := DRUQConicAux.sec5_core amb hM hK hE hS S t
      (sInf Pr) (fun μ hμ => csInf_le hbdd ⟨μ, hμ, rfl⟩)
    exact hobj.trans (hu ⟨γ, lam, kap, φ, τ, ψ, hfeas, rfl⟩)
