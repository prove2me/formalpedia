-- Prove2me | solution 1 for CtxInvOpt.Offline.Supplement.theorem4_projected_cones_regret_false
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:12:40.924181+00:00
-- url     : https://prove2.me/submissions/15625172-324d-4bde-985f-d618d9c9dbbe

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Supplement_Run
import Definitions.Def_CtxInvOpt_Greedy_Online

open CtxInvOpt
open CtxInvOpt.Offline
open CtxInvOpt.Offline.Supplement

theorem solution :
    ∀ (d n : ℕ), 2 ≤ d → 1 ≤ n → ∀ (K : ℝ) (T0 : ℕ),
      ∃ T : ℕ, T0 ≤ T ∧ 0 < T ∧
        ∃ (cstar : EuclideanSpace ℝ (Fin d)) (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
          (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
          (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (S : ℕ → Option (PCFrame d)),
          cstar ∈ CtxInvOpt.Offline.unitSphere d ∧
          (∀ t, CtxInvOpt.Offline.IsActionSet (X t)) ∧
          (∀ t, CtxInvOpt.Offline.IsContext (f t)) ∧
          IsProjConesRun ((d : ℝ) / T) ((d : ℝ) / T / (2 * d)) cstar X f xpi xstar S ∧
          K * (d : ℝ) ^ 4 * Real.log T < CtxInvOpt.Greedy.cumRegret cstar f xpi xstar T := by
            open Matrix Real in
            intro d n hd hn K T0
            obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
            obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
            obtain ⟨N, P, hNP, hP, hNT0, hNd, hNK, hN2⟩ : ∃ N P : ℕ, N = 2*P+2 ∧ 1 ≤ P ∧ T0 ≤ N ∧ (d'+2)^2 < N ∧
                256 * |K| * ((d':ℝ)+2)^4 < N ∧ 2 ≤ N := by
              refine ⟨2 * (T0 + (d'+2)^2 + ⌈256 * |K| * ((d':ℝ)+2)^4⌉₊ + 1) + 2,
                T0 + (d'+2)^2 + ⌈256 * |K| * ((d':ℝ)+2)^4⌉₊ + 1, rfl, by omega, by omega, by omega, ?_, by omega⟩
              have := Nat.le_ceil (256 * |K| * ((d':ℝ)+2)^4)
              have := Nat.cast_nonneg (α := ℝ) ⌈256 * |K| * ((d':ℝ)+2)^4⌉₊
              push_cast
              have : (0:ℝ) ≤ (T0:ℝ) + ((d':ℝ)+2)^2 := by positivity
              linarith
            have hT : T0 ≤ N^4 := le_trans hNT0 (Nat.le_self_pow (by norm_num) N)
            refine ⟨N^4, hT, by positivity, ?_⟩
            have hNpos : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
            have hN4pos : (0:ℝ) < (N:ℝ)^4 := by positivity
            have hN4ge : (16:ℝ) ≤ (N:ℝ)^4 := by
              have : (2:ℝ) ≤ N := by exact_mod_cast hN2
              have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) this 4
              norm_num at this; exact this
            set ε : ℝ := (((d'+2 : ℕ)) : ℝ) / ((N^4 : ℕ) : ℝ) with hε
            set η : ℝ := ε / (2 * (((d'+2 : ℕ)) : ℝ)) with hη
            have hη1 : η = 1 / (2 * (N:ℝ)^4) := by
              rw [hη, hε]; push_cast; field_simp
            have hηpos : 0 < η := by rw [hη1]; positivity
            have hηle : η ≤ 1/2 := by
              rw [hη1]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith only [hN4ge])
            have hε2 : ε ^ 2 < 1 / (N:ℝ)^4 := by
              rw [hε]; push_cast
              have hd2 : (((d':ℝ)+2))^2 < N := by exact_mod_cast hNd
              rw [div_pow, div_lt_div_iff₀ (by positivity) hN4pos]
              have hNN : (N:ℝ) ≤ (N:ℝ)^4 := by
                have : (1:ℝ) ≤ N := by linarith [show (2:ℝ) ≤ N by exact_mod_cast hN2]
                simpa using pow_le_pow_right₀ this (show 1 ≤ 4 by norm_num)
              rw [one_mul, sq ((N:ℝ)^4)]
              exact mul_lt_mul_of_pos_right (lt_of_lt_of_le hd2 hNN) hN4pos
            clear_value ε η
            -- vectors
            set e0 : EuclideanSpace ℝ (Fin (d'+2)) := EuclideanSpace.single 0 1 with he0
            set e1 : EuclideanSpace ℝ (Fin (d'+2)) := EuclideanSpace.single 1 1 with he1
            have h01 : (0 : Fin (d'+2)) ≠ 1 := by simp [Fin.ext_iff]
            have hinner : ∀ a b c c' : ℝ, inner ℝ (a • e0 + b • e1) (c • e0 + c' • e1) = a * c + b * c' := by
              intro a b c c'
              simp [e0, e1, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
                EuclideanSpace.inner_single_left, h01, h01.symm]
              ring
            have hnorm : ∀ a b : ℝ, ‖a • e0 + b • e1‖ = √(a^2 + b^2) := by
              intro a b
              rw [norm_eq_sqrt_real_inner, hinner]; ring_nf
            have he0P : e0 = (1:ℝ) • e0 + (0:ℝ) • e1 := by simp
            have he1P : e1 = (0:ℝ) • e0 + (1:ℝ) • e1 := by simp
            obtain ⟨B2, hB2v, hB2T, hB2B2, hB2rows⟩ : ∃ B2 : Matrix (Fin 2) (Fin (d'+2)) ℝ,
                (∀ a b : ℝ, B2 *ᵥ WithLp.ofLp (a • e0 + b • e1) = ![a, b]) ∧
                (∀ x : Fin 2 → ℝ, (WithLp.toLp 2 (B2ᵀ *ᵥ x) : EuclideanSpace ℝ (Fin (d'+2))) = x 0 • e0 + x 1 • e1) ∧
                B2 * B2ᵀ = 1 ∧
                (fun k => (WithLp.toLp 2 (B2 k) : EuclideanSpace ℝ (Fin (d'+2)))) = ![e0, e1] := by
              refine ⟨Matrix.of ![WithLp.ofLp e0, WithLp.ofLp e1], ?_, ?_, ?_, ?_⟩
              · intro a b
                ext k; fin_cases k <;> simp [e0, e1, Matrix.mulVec, h01, h01.symm]
              · intro x
                ext j
                simp [e0, e1, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.single_apply]
              · ext k l; fin_cases k <;> fin_cases l <;> simp [e0, e1, Matrix.mul_apply, Pi.single_apply, h01, h01.symm]
              · funext k; fin_cases k <;> rfl
            have hB2e0 : B2 *ᵥ WithLp.ofLp e0 = ![1, 0] := by rw [he0P, hB2v]
            have hB2e1 : B2 *ᵥ WithLp.ofLp e1 = ![0, 1] := by rw [he1P, hB2v]
            have hfb : firstBasisVec (d'+2) = e0 := by
              ext j; simp only [firstBasisVec, e0, PiLp.single_apply, WithLp.ofLp_toLp, Fin.val_eq_zero_iff]
            have hcn : coordNorm (![1/2, 1/2] : Fin 2 → ℝ) = √2 / 2 := by
              unfold coordNorm
              rw [show (![1/2, 1/2] : Fin 2 → ℝ) ⬝ᵥ ![1/2, 1/2] = (√2/2)^2 by
                simp [dotProduct, Fin.sum_univ_two, div_pow, Real.sq_sqrt]; norm_num]
              exact Real.sqrt_sq (by positivity)
            have hPC : let chat : Fin 2 → ℝ := ![1/2, 1/2]
                IsPolyCenter ![e0, e1] B2 ((coordNorm chat)⁻¹ • chat) (π/4) := by
              intro chat
              have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
              have hs2pos : 0 < √2 := by positivity
              have hcn : coordNorm chat = √2 / 2 := by
                unfold coordNorm
                rw [show chat ⬝ᵥ chat = (√2/2)^2 by
                  simp [chat, dotProduct, Fin.sum_univ_two, div_pow, Real.sq_sqrt]; norm_num]
                exact Real.sqrt_sq (by positivity)
              unfold IsPolyCenter
              intro δbar zt z
              have hδbar : δbar = ![![1, 0], ![0, 1]] := by
                funext i; fin_cases i <;> simp [δbar, hB2e0, hB2e1]
              have hzt : zt = ![1, 1] := by
                simp only [zt, hδbar]; ext i; fin_cases i <;> simp [Fin.sum_univ_two]
              have hz : z = ![(√2)⁻¹, (√2)⁻¹] := by
                have : coordNorm zt = √2 := by
                  unfold coordNorm; rw [hzt]; simp [dotProduct, Fin.sum_univ_succ]; norm_num
                simp only [z]; rw [this, hzt]; ext i; fin_cases i <;> simp
              rw [hz]
              refine ⟨![![√2, 0], ![0, √2]], ?_, ?_, ![![1, 0], ![0, 1]], ?_, chat, ?_, ?_, rfl, ?_⟩
              · intro k
                rw [hδbar]
                fin_cases k <;> refine ⟨?_, ?_⟩ <;> simp [dotProduct, Fin.sum_univ_two, hs2pos.ne']
              · intro k c ⟨hc1, hc2⟩
                rw [hδbar] at hc2
                simp [dotProduct, Fin.sum_univ_two] at hc1
                fin_cases k
                · have := hc2 1 (by decide); simp [dotProduct, Fin.sum_univ_two] at this
                  rw [this] at hc1
                  ext j; fin_cases j <;> simp
                  · field_simp at hc1; linarith
                  · exact this
                · have := hc2 0 (by decide); simp [dotProduct, Fin.sum_univ_two] at this
                  rw [this] at hc1
                  ext j; fin_cases j <;> simp
                  · exact this
                  · field_simp at hc1; linarith
              · intro k
                have h1 : coordNorm ![√2, (0:ℝ)] = √2 := by
                  unfold coordNorm; simp [dotProduct, Fin.sum_univ_two, hs2]
                have h2 : coordNorm ![(0:ℝ), √2] = √2 := by
                  unfold coordNorm; simp [dotProduct, Fin.sum_univ_two, hs2]
                fin_cases k <;> ext j <;> fin_cases j <;> simp [h1, h2, hs2pos.ne']
              · have := (convex_convexHull ℝ (Set.range ![![(1:ℝ), 0], ![0, 1]]))
                  (subset_convexHull ℝ _ ⟨0, rfl⟩) (subset_convexHull ℝ _ ⟨1, rfl⟩)
                  (a := 1/2) (b := 1/2) (by norm_num) (by norm_num) (by norm_num)
                convert this using 1
                ext j; fin_cases j <;> simp [chat]
              · intro c hc
                have hH : convexHull ℝ (Set.range ![![(1:ℝ), 0], ![0, 1]]) ⊆ {c : Fin 2 → ℝ | c 0 + c 1 = 1} := by
                  apply convexHull_min
                  · rintro _ ⟨i, rfl⟩; fin_cases i <;> simp
                  · intro x hx y hy a b ha hb hab
                    simp only [Set.mem_setOf_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx hy ⊢
                    linear_combination a * hx + b * hy + hab
                have := hH hc
                simp only [Set.mem_setOf_eq] at this
                simp [chat, dotProduct, Fin.sum_univ_two]
                nlinarith only [sq_nonneg (c 0 - c 1), this]
              · have hq : (fun k => chat ⬝ᵥ ![![(1:ℝ), 0], ![0, 1]] k) = fun _ => 1/2 := by
                  funext k; fin_cases k <;> simp [chat, dotProduct, Fin.sum_univ_two]
                rw [hq, Finset.inf'_const, hcn]
                rw [show (√2 / 2)⁻¹ * (1/2 : ℝ) = √2 / 2 by field_simp; rw [sq, hs2]]
                rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
            clear_value e0 e1
            obtain ⟨rot, hrot⟩ : ∃ rot : ℝ → Matrix (Fin 2) (Fin 2) ℝ,
                ∀ θ, rot θ = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ] := ⟨_, fun _ => rfl⟩
            have hrot_orth : ∀ θ, rot θ ∈ Matrix.orthogonalGroup (Fin 2) ℝ := by
              intro θ
              rw [Matrix.mem_orthogonalGroup_iff, hrot]
              ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
                first | ring1 | linear_combination Real.sin_sq_add_cos_sq θ | linear_combination Real.cos_sq_add_sin_sq θ
            have hrot_add : ∀ θ σ, rot (θ + σ) = rot θ * rot σ := by
              intro θ σ
              rw [hrot, hrot, hrot]
              ext i j; fin_cases i <;> fin_cases j <;>
                simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring
            have hCU : ∀ w φ s : ℝ, s = 1 ∨ s = -1 →
                let δ := (-(s * sin φ)) • e0 + (s * cos φ) • e1
                subspaceProj B2 δ = δ ∧
                CtxInvOpt.Pointed.tailQuad (fun _ : Fin 1 => w) ((rot φ)ᵀ *ᵥ (B2 *ᵥ WithLp.ofLp (subspaceProj B2 δ))) = w ∧
                IsConeUpdateEta η B2 (fun _ => w) (rot φ) (subspaceProj B2 δ) (fun _ => w/2 + η)
                  (rot (φ + arctan (((1 + -(η * s)) / 2) * (√w * s)))) := by
              intro w φ s hs δ
              have hs2 : s * s = 1 := by rcases hs with h | h <;> subst h <;> norm_num
              have hP : subspaceProj B2 δ = δ := by
                unfold subspaceProj
                rw [hB2v, hB2T]; simp [δ]
              have hv : (rot φ)ᵀ *ᵥ (B2 *ᵥ WithLp.ofLp (subspaceProj B2 δ)) = ![0, s] := by
                rw [hP, hB2v, hrot]
                ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
                · ring
                · linear_combination s * sin_sq_add_cos_sq φ
              refine ⟨hP, ?_, ?_⟩
              · rw [hv]; simp [CtxInvOpt.Pointed.tailQuad]
                rcases hs with h | h <;> subst h <;> norm_num
              · unfold IsConeUpdateEta
                rw [hv]
                have htail : (coordNorm (CtxInvOpt.Pointed.tailVec ![0, s]))⁻¹ • CtxInvOpt.Pointed.tailVec ![0, s]
                    = fun _ : Fin 1 => s := by
                  have : coordNorm (CtxInvOpt.Pointed.tailVec ![(0:ℝ), s]) = 1 := by
                    unfold coordNorm; simp [CtxInvOpt.Pointed.tailVec, dotProduct, hs2]
                  rw [this]; funext i; simp [CtxInvOpt.Pointed.tailVec]
                intro v δbar
                have hδ : δbar = fun _ => s := htail
                rw [if_pos rfl]
                intro β b a
                set a0 := ((1 + -(η * s)) / 2) * (√w * s) with ha0
                have ha : a = fun _ => a0 := by funext i; simp only [a, b, β, hδ, ha0]
                rw [ha]
                refine ⟨fun _ => rfl, rot (arctan a0), ?_, ?_, ?_⟩
                · exact hrot_orth _
                · intro i
                  have hd : (1 + (fun _ : Fin 1 => a0) ⬝ᵥ (fun _ : Fin 1 => a0)) = 1 + a0 ^ 2 := by
                    simp [dotProduct]; ring
                  rw [hd, hrot]
                  fin_cases i
                  · simp [cos_arctan]
                  · simp [sin_arctan]
                · exact hrot_add _ _
            -- dynamics
            obtain ⟨sg, hsg⟩ : ∃ sg : ℝ → ℝ, ∀ x, sg x = if x ≤ 0 then 1 else -1 := ⟨_, fun _ => rfl⟩
            have hsg1 : ∀ x, sg x = 1 ∨ sg x = -1 := by
              intro x; rw [hsg]; split_ifs <;> simp
            obtain ⟨g, hg0, hgs⟩ : ∃ g : ℕ → ℝ × ℝ, g 0 = (π/4, 1) ∧ ∀ k, g (k+1) =
                ((g k).1 + Real.arctan (((1 + -(η * sg (g k).1)) / 2) * (√((g k).2) * sg (g k).1)),
                  (g k).2 / 2 + η) :=
              ⟨fun k => Nat.rec (π/4, 1) (fun _ p => (p.1 + Real.arctan (((1 + -(η * sg p.1)) / 2) *
                (√(p.2) * sg p.1)), p.2 / 2 + η)) k, rfl, fun _ => rfl⟩
            have harc : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → x / 2 ≤ Real.arctan x := by
              intro x hx0 hx1
              have h1 := Real.sin_le (Real.arctan_nonneg.mpr hx0)
              rw [Real.sin_arctan] at h1
              have h2 : √(1 + x^2) ≤ 2 := by
                rw [show (2:ℝ) = √4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
                have hxx : x^2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hx1 hx0 hx1
                exact Real.sqrt_le_sqrt (by linarith only [hxx])
              have h3 : 0 < √(1 + x^2) := Real.sqrt_pos.mpr (by positivity)
              have h4 : x / 2 ≤ x / √(1 + x^2) := div_le_div_of_nonneg_left hx0 h3 h2
              linarith
            have hinv : ∀ k, |(g k).1| ≤ π/2 ∧ 1 / (N:ℝ)^4 ≤ (g k).2 ∧ (g k).2 ≤ 1 := by
              intro k
              induction k with
              | zero =>
                rw [hg0]; refine ⟨?_, ?_, le_refl _⟩
                · rw [abs_of_pos (by positivity)]; linarith only [Real.pi_pos]
                · rw [div_le_one hN4pos]; linarith only [hN4ge]
              | succ k ih =>
                obtain ⟨h1, h2, h3⟩ := ih
                have hw0 : 0 ≤ (g k).2 := le_trans (by positivity) h2
                rw [hgs k]
                refine ⟨?_, ?_, ?_⟩
                · dsimp only
                  have hlt := Real.arctan_lt_pi_div_two (((1 + -(η * sg (g k).1)) / 2) * (√((g k).2) * sg (g k).1))
                  have hgt := Real.neg_pi_div_two_lt_arctan (((1 + -(η * sg (g k).1)) / 2) * (√((g k).2) * sg (g k).1))
                  rw [abs_le] at h1 ⊢
                  by_cases hφ : (g k).1 ≤ 0
                  · have hs : sg (g k).1 = 1 := by rw [hsg, if_pos hφ]
                    have : 0 ≤ Real.arctan (((1 + -(η * sg (g k).1)) / 2) * (√((g k).2) * sg (g k).1)) := by
                      rw [Real.arctan_nonneg, hs]
                      exact mul_nonneg (div_nonneg (by linarith only [hηle]) (by norm_num)) (mul_nonneg (Real.sqrt_nonneg _) (by norm_num))
                    constructor <;> linarith only [h1.1, h1.2, hφ, this, hlt, hgt]
                  · have hs : sg (g k).1 = -1 := by rw [hsg, if_neg hφ]
                    have : Real.arctan (((1 + -(η * sg (g k).1)) / 2) * (√((g k).2) * sg (g k).1)) ≤ 0 := by
                      rw [hs, show ((1 + -(η * -1)) / 2) * (√((g k).2) * -1) = -(((1 + η) / 2) * √((g k).2)) by ring,
                        Real.arctan_neg, neg_nonpos, Real.arctan_nonneg]
                      exact mul_nonneg (by linarith only [hηpos]) (Real.sqrt_nonneg _)
                    push_neg at hφ
                    constructor <;> linarith only [h1.1, h1.2, hφ, this, hlt, hgt]
                · dsimp only; rw [hη1]
                  have : 1 / (N:ℝ)^4 = 1 / (N:ℝ)^4 / 2 + 1 / (2 * (N:ℝ)^4) := by field_simp; ring
                  linarith only [h2, this]
                · show (g k).2 / 2 + η ≤ 1
                  linarith only [h3, hηle]
            have hσ : ∀ k, 1 / (8 * (N:ℝ)^2) ≤ |(g (k+1)).1 - (g k).1| := by
              intro k
              obtain ⟨h1, h2, h3⟩ := hinv k
              rw [hgs k]; dsimp only
              rw [add_sub_cancel_left]
              have hsq : 1 / (N:ℝ)^2 ≤ √((g k).2) := by
                rw [Real.le_sqrt (by positivity) (le_trans (by positivity) h2)]
                rw [div_pow, one_pow, ← pow_mul]; exact h2
              have hsq1 : √((g k).2) ≤ 1 := Real.sqrt_le_one.mpr h3
              have h8 : 1 / (8 * (N:ℝ)^2) = (1 / 4) * (1 / (N:ℝ)^2) / 2 := by field_simp; ring
              have hN2pos : 0 < 1 / (N:ℝ)^2 := by positivity
              by_cases hφ : (g k).1 ≤ 0
              · have hs : sg (g k).1 = 1 := by rw [hsg, if_pos hφ]
                rw [hs, mul_one, mul_one]
                set x := (1 + -η) / 2 * √((g k).2) with hx
                have hx0 : (1/4) * (1 / (N:ℝ)^2) ≤ x := by
                  rw [hx]; exact mul_le_mul (by linarith only [hηle]) hsq hN2pos.le (by linarith only [hηle])
                have hx1 : x ≤ 1 := by
                  rw [hx]; exact mul_le_one₀ (by linarith only [hηpos]) (Real.sqrt_nonneg _) hsq1
                have := harc x (by linarith only [hx0, hN2pos]) hx1
                rw [abs_of_nonneg (Real.arctan_nonneg.mpr (by linarith only [hx0, hN2pos]))]
                refine le_trans ?_ this
                rw [h8]; linarith only [hx0]
              · have hs : sg (g k).1 = -1 := by rw [hsg, if_neg hφ]
                rw [hs, show ((1 + -(η * -1)) / 2) * (√((g k).2) * -1) = -(((1 + η) / 2) * √((g k).2)) by ring,
                  Real.arctan_neg, abs_neg]
                set x := (1 + η) / 2 * √((g k).2) with hx
                have hx0 : (1/4) * (1 / (N:ℝ)^2) ≤ x := by
                  rw [hx]; exact mul_le_mul (by linarith only [hηpos]) hsq hN2pos.le (by linarith only [hηpos])
                have hx1 : x ≤ 1 := by
                  rw [hx]; exact mul_le_one₀ (by linarith only [hηle]) (Real.sqrt_nonneg _) hsq1
                have := harc x (by linarith only [hx0, hN2pos]) hx1
                rw [abs_of_nonneg (Real.arctan_nonneg.mpr (by linarith only [hx0, hN2pos]))]
                refine le_trans ?_ this
                rw [h8]; linarith only [hx0]
            have hr : ∀ k, (2 / π) * |(g k).1| ≤ -(sg (g k).1 * Real.sin (g k).1) := by
              intro k
              obtain ⟨h1, -, -⟩ := hinv k
              rw [abs_le] at h1
              by_cases hφ : (g k).1 ≤ 0
              · rw [hsg, if_pos hφ, abs_of_nonpos hφ, one_mul, ← Real.sin_neg]
                exact Real.mul_le_sin (by linarith) (by linarith)
              · push_neg at hφ
                rw [hsg, if_neg (not_le.mpr hφ), abs_of_pos hφ]
                have := Real.mul_le_sin hφ.le h1.2
                linarith
            obtain ⟨ca, cb, hca0, hca1, hca2, hcb0, hcb1, hcb2⟩ : ∃ ca cb : ℕ → ℝ, ca 0 = 0 ∧ ca 1 = 1 ∧
                (∀ k, ca (k+2) = -(sg (g k).1 * sin (g k).1)) ∧ cb 0 = 1 ∧ cb 1 = 0 ∧
                (∀ k, cb (k+2) = sg (g k).1 * cos (g k).1) :=
              ⟨fun t => Nat.casesOn (motive := fun _ => ℝ) t 0
                  (fun t => Nat.casesOn (motive := fun _ => ℝ) t 1 (fun k => -(sg (g k).1 * sin (g k).1))),
               fun t => Nat.casesOn (motive := fun _ => ℝ) t 1
                  (fun t => Nat.casesOn (motive := fun _ => ℝ) t 0 (fun k => sg (g k).1 * cos (g k).1)),
               rfl, rfl, fun _ => rfl, rfl, rfl, fun _ => rfl⟩
            have hsq : ∀ t, ca t ^ 2 + cb t ^ 2 = 1 := by
              intro t
              rcases t with _ | _ | k
              · rw [hca0, hcb0]; norm_num
              · rw [hca1, hcb1]; norm_num
              · rw [hca2, hcb2]
                have := sin_sq_add_cos_sq (g k).1
                rcases hsg1 (g k).1 with h | h <;> rw [h] <;> linear_combination this
            have hcapos : ∀ t, 0 ≤ ca t := by
              intro t
              rcases t with _ | _ | k
              · rw [hca0]
              · rw [hca1]; norm_num
              · rw [hca2]; exact le_trans (by have := abs_nonneg (g k).1; have := Real.pi_pos; positivity) (hr k)
            obtain ⟨D, hDdef⟩ : ∃ D : ℕ → EuclideanSpace ℝ (Fin (d'+2)), ∀ t, D t = ca t • e0 + cb t • e1 :=
              ⟨_, fun _ => rfl⟩
            have hDnorm : ∀ t, ‖D t‖ = 1 := by intro t; rw [hDdef, hnorm, hsq, Real.sqrt_one]
            have hDne : ∀ t, D t ≠ 0 := by
              intro t h; have := hDnorm t; rw [h, norm_zero] at this; norm_num at this
            have hin0 : ∀ t, inner ℝ (D t) e0 = ca t := by
              intro t
              have := hinner (ca t) (cb t) 1 0
              rw [one_smul, zero_smul, add_zero, mul_one, mul_zero, add_zero] at this
              rw [hDdef]; exact this
            obtain ⟨u, hu⟩ : ∃ u : EuclideanSpace ℝ (Fin (n'+1)), u = EuclideanSpace.single 0 1 := ⟨_, rfl⟩
            have huu : inner ℝ u u = (1:ℝ) := by simp [hu]
            have hunorm : ‖u‖ = 1 := by simp [hu]
            obtain ⟨f, hf⟩ : ∃ f : ℕ → EuclideanSpace ℝ (Fin (n'+1)) → EuclideanSpace ℝ (Fin (d'+2)),
                ∀ t x, f t x = (inner ℝ u x) • D t := ⟨_, fun _ _ => rfl⟩
            have hfi : ∀ t y c, inner ℝ (f t y) c = inner ℝ u y * inner ℝ (D t) c := by
              intro t y c; rw [hf, real_inner_smul_left]
            have heff : (fun s => CtxInvOpt.Pointed.effDiff (f s u - f s 0)) = D := by
              funext s
              rw [hf, hf, huu, inner_zero_right, zero_smul, sub_zero, one_smul]
              unfold CtxInvOpt.Pointed.effDiff; rw [if_neg (hDne s), hDnorm, inv_one, one_smul]
            obtain ⟨S, hS0, hS1, hS2⟩ : ∃ S : ℕ → Option (PCFrame (d'+2)), S 0 = none ∧
                S 1 = some ⟨0, fun _ => 0, Matrix.of (fun _ j => WithLp.ofLp (D 0) j), Fin.elim0, 1⟩ ∧
                ∀ k, S (k+2) = some ⟨1, Fin.cons 1 (fun _ => 0), B2, fun _ => (g k).2, rot (g k).1⟩ :=
              ⟨fun t => Nat.casesOn (motive := fun _ => Option (PCFrame (d'+2))) t none
                (fun t => Nat.casesOn (motive := fun _ => Option (PCFrame (d'+2))) t
                  (some ⟨0, fun _ => 0, Matrix.of (fun _ j => WithLp.ofLp (D 0) j), Fin.elim0, 1⟩)
                  (fun k => some ⟨1, Fin.cons 1 (fun _ => 0), B2, fun _ => (g k).2, rot (g k).1⟩)),
                rfl, rfl, fun _ => rfl⟩
            have hpx0 : pcProxy (S 0) = e0 := by rw [hS0]; exact hfb
            have hpx1 : pcProxy (S 1) = D 0 := by
              rw [hS1]; ext j; simp [pcProxy, Matrix.mulVec, dotProduct]
            have hpx2 : ∀ k, pcProxy (S (k+2)) = cos (g k).1 • e0 + sin (g k).1 • e1 := by
              intro k; rw [hS2]
              show WithLp.toLp 2 (B2ᵀ *ᵥ _) = _
              rw [hB2T, hrot]; simp
            have hperp : ∀ t, inner ℝ (D t) (pcProxy (S t)) = 0 := by
              intro t
              rcases t with _ | _ | k
              · rw [hpx0, hin0, hca0]
              · rw [hpx1, hDdef, hDdef, hinner, hca1, hcb1, hca0, hcb0]; ring
              · rw [hpx2, hDdef, hinner, hca2, hcb2]; ring
            have hstep : ∀ t, IsPCStep ε η D t (S t) (S (t+1)) := by
              intro t
              rcases t with _ | _ | k
              · rw [hS0, hS1]; exact ⟨fun h => absurd h (hDne 0), fun _ => rfl⟩
              · rw [hS1, show 1 + 1 = 0 + 2 from rfl, hS2 0]
                have hBv : (Matrix.of (fun (_ : Fin 1) j => WithLp.ofLp (D 0) j)) *ᵥ WithLp.ofLp (D 1) = 0 := by
                  have h := hperp 1
                  rw [hpx1] at h
                  funext i
                  rw [Pi.zero_apply, ← h]
                  simp [Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
                have hproj : subspaceProj (Matrix.of (fun (_ : Fin 1) j => WithLp.ofLp (D 0) j)) (D 1) = 0 := by
                  unfold subspaceProj; rw [hBv, Matrix.mulVec_zero]; rfl
                refine ⟨fun h => absurd h ?_, fun _ => ?_⟩
                · dsimp only
                  rw [hproj, sub_zero, hDnorm]; linarith
                · have hfam : (fun k : Fin 2 => D ((Fin.cons 1 (fun _ : Fin 1 => 0) : Fin 2 → ℕ) k)) = ![e0, e1] := by
                    funext k; fin_cases k
                    · simp only [Fin.zero_eta, Fin.isValue, Fin.cons_zero, Matrix.cons_val_zero]
                      rw [hDdef, hca1, hcb1, ← he0P]
                    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
                      rw [show (Fin.cons 1 (fun _ : Fin 1 => 0) : Fin 2 → ℕ) 1 = 0 from rfl]
                      rw [hDdef, hca0, hcb0, ← he1P]
                  refine ⟨B2, (coordNorm (![1/2, 1/2] : Fin 2 → ℝ))⁻¹ • ![1/2, 1/2], π/4, rot (π/4), hB2B2, ?_, ?_,
                    hrot_orth _, ?_, ?_⟩
                  · dsimp only
                    rw [hfam, hB2rows]
                  · dsimp only
                    rw [hfam]; exact hPC
                  · intro i
                    have hs2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
                    have hs2pos : 0 < √2 := by positivity
                    have hh : (√2 / 2)⁻¹ * (1/2 : ℝ) = √2 / 2 := by field_simp; rw [sq, hs2]
                    rw [hrot, hcn]
                    fin_cases i <;> simp [Real.cos_pi_div_four, Real.sin_pi_div_four] <;> ring
                  · rw [hg0, Real.tan_pi_div_four]; simp
              · rw [hS2 k, show k + 1 + 1 + 1 = (k+1) + 2 from rfl, hS2 (k+1), hgs k]
                obtain ⟨hP, hQ, hC⟩ := hCU (g k).2 (g k).1 (sg (g k).1) (hsg1 _)
                have hD2 : D (k+1+1) = (-(sg (g k).1 * sin (g k).1)) • e0 + (sg (g k).1 * cos (g k).1) • e1 := by
                  rw [hDdef, hca2, hcb2]
                unfold IsPCStep
                dsimp only
                rw [hD2]
                refine ⟨fun _ => ⟨fun h => absurd h ?_, fun _ => ⟨_, _, hC, rfl⟩⟩, fun h => absurd h ?_⟩
                · rw [hQ]; exact not_le.mpr (lt_of_lt_of_le hε2 (hinv k).2.1)
                · rw [hP, sub_self, norm_zero]; exact not_lt.mpr hηpos.le
            have hxpi : ∀ t, u ∈ CtxInvOpt.Offline.argminSet (pcProxy (S t)) {0, u} (f t) := by
              intro t
              refine ⟨by simp, fun y _ => ?_⟩
              rw [hfi, hfi, hperp, mul_zero, mul_zero]
            have hxstar : ∀ t, (0 : EuclideanSpace ℝ (Fin (n'+1))) ∈ CtxInvOpt.Offline.argminSet e0 {0, u} (f t) := by
              intro t
              refine ⟨by simp, fun y hy => ?_⟩
              rw [hfi, hfi, inner_zero_right, zero_mul, hin0]
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl
              · simp
              · rw [huu, one_mul]; exact hcapos t
            refine ⟨e0, fun _ => {0, u}, f, fun _ => u, fun _ => 0, S, ?_, ?_, ?_, ?_, ?_⟩
            · show e0 ∈ Metric.sphere 0 1
              rw [mem_sphere_zero_iff_norm, he0P, hnorm]; norm_num
            · intro t
              refine ⟨⟨0, by simp⟩, (Set.toFinite _).isCompact, ?_⟩
              rw [Metric.diam_pair, dist_eq_norm, zero_sub, norm_neg, hunorm]
            · intro t
              refine LipschitzWith.of_dist_le_mul fun x y => ?_
              rw [hf, hf, dist_eq_norm, dist_eq_norm, ← sub_smul, ← inner_sub_right, norm_smul, hDnorm, mul_one,
                Real.norm_eq_abs, NNReal.coe_one, one_mul]
              calc |inner ℝ u (x - y)| ≤ ‖u‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
                _ = ‖x - y‖ := by rw [hunorm, one_mul]
            · refine ⟨hS0, fun t => ⟨hxpi t, hxstar t, ?_⟩⟩
              show IsPCStep ε η (fun s => CtxInvOpt.Pointed.effDiff (f s u - f s 0)) t (S t) (S (t+1))
              rw [heff]; exact hstep t
            · have hreg : CtxInvOpt.Greedy.cumRegret e0 f (fun _ => u) (fun _ => 0) (N^4)
                  = ∑ t ∈ Finset.range (N^4), ca t := by
                unfold CtxInvOpt.Greedy.cumRegret
                refine Finset.sum_congr rfl fun t _ => ?_
                rw [hf, hf, huu, inner_zero_right, zero_smul, sub_zero, one_smul, hin0]
              have hMle : 2 * (N^3 * P) + 2 ≤ N^4 := by
                have h1 : 1 ≤ N^3 := Nat.one_le_pow _ _ (by omega)
                have h2 : N^4 = N^3 * N := by ring
                have h3 : N^3 * N = N^3 * (2*P+2) := by rw [← hNP]
                rw [h2, h3, show N^3*(2*P+2) = 2*(N^3*P) + 2*N^3 by ring]; omega
              have hpair : ∀ M : ℕ, (M:ℝ) * (1 / (8 * (N:ℝ)^2)) ≤ ∑ k ∈ Finset.range (2*M), |(g k).1| := by
                intro M; induction M with
                | zero => simp
                | succ M ih =>
                  rw [show 2*(M+1) = 2*M+1+1 by ring, Finset.sum_range_succ, Finset.sum_range_succ]
                  have := hσ (2*M)
                  have h2 : |(g (2*M+1)).1 - (g (2*M)).1| ≤ |(g (2*M+1)).1| + |(g (2*M)).1| := abs_sub _ _
                  push_cast; linarith only [ih, this, h2]
              have hsum1 : ∑ k ∈ Finset.range (2*(N^3*P)+2), ca k ≤ ∑ t ∈ Finset.range (N^4), ca t :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hMle) (fun i _ _ => hcapos i)
              have hsum2 : (2/π) * ∑ k ∈ Finset.range (2*(N^3*P)), |(g k).1| ≤ ∑ k ∈ Finset.range (2*(N^3*P)+2), ca k := by
                rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
                have : ∑ i ∈ Finset.range (2*(N^3*P)), 2/π * |(g i).1| ≤ ∑ i ∈ Finset.range (2*(N^3*P)), ca (i+1+1) :=
                  Finset.sum_le_sum fun i _ => by rw [hca2]; exact hr i
                linarith only [this, hcapos 0, hcapos 1]
              have hpairM := mul_le_mul_of_nonneg_left (hpair (N^3*P)) (show (0:ℝ) ≤ 2/π by positivity)
              have hlog : Real.log ((N^4:ℕ):ℝ) = 4 * Real.log N := by
                push_cast; rw [Real.log_pow]; norm_num
              have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
              have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
              have hlogN : Real.log N ≤ N := le_trans (Real.log_le_sub_one_of_pos hNpos) (by linarith only [])
              have hd4 : (((d'+2:ℕ)):ℝ)^4 = ((d':ℝ)+2)^4 := by push_cast; ring
              have hd0 : 0 ≤ ((d':ℝ)+2)^4 := by positivity
              have hKabs : K * ((d':ℝ)+2)^4 * (4 * Real.log N) ≤ |K| * ((d':ℝ)+2)^4 * (4*N) := by
                have h1 : K ≤ |K| := le_abs_self K
                calc K * ((d':ℝ)+2)^4 * (4 * Real.log N) ≤ |K| * ((d':ℝ)+2)^4 * (4 * Real.log N) :=
                      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hd0) (by linarith only [hlogN0])
                  _ ≤ |K| * ((d':ℝ)+2)^4 * (4*N) :=
                      mul_le_mul_of_nonneg_left (by linarith only [hlogN]) (mul_nonneg (abs_nonneg K) hd0)
              have hPr : (N:ℝ) = 2 * P + 2 := by exact_mod_cast hNP
              have hP1 : (1:ℝ) ≤ P := by exact_mod_cast hP
              have key : |K| * ((d':ℝ)+2)^4 * (4*N) < (2/π) * ((((N^3*P : ℕ)) : ℝ) * (1 / (8 * (N:ℝ)^2))) := by
                have e : (2/π) * ((((N^3*P : ℕ)) : ℝ) * (1 / (8 * (N:ℝ)^2))) = N * P / (4*π) := by
                  push_cast; field_simp; ring
                rw [e, lt_div_iff₀ (by positivity)]
                set A := |K| * ((d':ℝ)+2)^4 with hA
                have hA1 : A < N / 256 := by rw [hA]; linarith only [hNK]
                have hA0 : 0 ≤ A := by positivity
                have h1 : A * (16 * N * π) < (N / 256) * (16 * N * π) :=
                  mul_lt_mul_of_pos_right hA1 (by positivity)
                have h2 : (N / 256) * (16 * N * π) ≤ (N:ℝ)^2 / 4 := by
                  have := Real.pi_le_four
                  have : (N:ℝ) * N * π ≤ N * N * 4 := mul_le_mul_of_nonneg_left Real.pi_le_four (by positivity)
                  have e : (N / 256) * (16 * N * π) = ((N:ℝ)*N*π)/16 := by ring
                  rw [e, sq]; linarith only [this]
                have h3 : (N:ℝ)^2 / 4 ≤ N * P := by
                  have hPP : (1:ℝ) ≤ P * P := by
                    have := mul_le_mul hP1 hP1 zero_le_one (by linarith only [hP1]); rwa [one_mul] at this
                  rw [hPr, show ((2:ℝ) * P + 2) ^ 2 / 4 = P * P + 2 * P + 1 by ring,
                    show ((2:ℝ) * P + 2) * P = 2 * (P * P) + 2 * P by ring]
                  linarith only [hPP]
                have e2 : A * (4 * N) * (4 * π) = A * (16 * N * π) := by ring
                rw [e2]; linarith only [h1, h2, h3]
              rw [hreg, hlog, hd4]
              exact lt_of_le_of_lt hKabs (lt_of_lt_of_le key (hpairM.trans (hsum2.trans hsum1)))
