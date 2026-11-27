-- Prove2me | solution 1 for ConeLifts.Factorization.Supplement.coneRank_eq_least_lift
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:27:34.21095+00:00
-- url     : https://prove2.me/submissions/05bacfd4-e158-45c0-8843-1019a48ed8ed

import Mathlib
import Definitions.Def_ConeLifts_Factorization_IsConvexBody
import Definitions.Def_ConeLifts_Factorization_HasLift
import Definitions.Def_ConeLifts_Factorization_Supplement_ConeFamily
import Definitions.Def_ConeLifts_Factorization_Supplement_coneRank

open ConeLifts
open ConeLifts.Factorization
open ConeLifts.Factorization.Supplement

/-- **Theorem 4.4** of Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, p. 13: "Let 𝒦 = (K_i)_{i≥0}
be a closed cone family and C ⊂ ℝⁿ a convex body. Then rank_𝒦(C) is the smallest i such that C
has a K_i-lift."

The smallest index is taken in `ℕ∞`, `⊤` when no `Kᵢ`-lift exists, so the two infinite cases
coincide as well. Recorded repair: `1 ≤ n`, as in Theorem 2.4 (for `n = 0` and `K₀ = ℝ⁰₊ = {0}`,
`C = {0} = ℝ⁰` has a `K₀`-lift but `𝒦`-rank at least `1`). -/
theorem solution {n : ℕ} (hn : 1 ≤ n) (𝒦 : ConeFamily) (h𝒦 : 𝒦.IsClosed)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : ConeLifts.Factorization.IsConvexBody C) :
    coneRank 𝒦 C =
      ⨅ (i : ℕ) (_ : ConeLifts.Factorization.HasLift (𝒦.cone i) C), (i : ℕ∞) := by
        · classical
          have hCS : ∀ m : ℕ, ContinuousSMul ℝ (EuclideanSpace ℝ (Fin m)) := fun m => inferInstance
          have Mk : ∀ k : ℕ, ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F],
              Module.finrank ℝ F = k → ∀ S : Set F, IsCompact S → Convex ℝ S →
              S ⊆ convexHull ℝ (Set.extremePoints ℝ S) := by
            intro k
            induction k using Nat.strong_induction_on with
            | _ k ih =>
            intro F _ _ _ hF
            -- case A: empty interior
            have caseA : ∀ S : Set F, IsCompact S → Convex ℝ S → interior S = ∅ →
                S ⊆ convexHull ℝ (Set.extremePoints ℝ S) := by
              intro S hS hSc hint x hx
              have hne : affineSpan ℝ S ≠ ⊤ := by
                intro h
                have := (hSc.interior_nonempty_iff_affineSpan_eq_top).mpr h
                rw [hint] at this
                exact Set.not_nonempty_empty this
              set V := (affineSpan ℝ S).direction with hV
              have hVne : V ≠ ⊤ := by
                intro h
                exact hne ((AffineSubspace.direction_eq_top_iff_of_nonempty
                  ⟨x, mem_affineSpan ℝ hx⟩).mp h)
              have hlt : Module.finrank ℝ V < k := hF ▸ Submodule.finrank_lt hVne
              have hmemV : ∀ s ∈ S, s - x ∈ V := fun s hs =>
                AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hs) (mem_affineSpan ℝ hx)
              let g : V →ᵃ[ℝ] F := ⟨fun v => (v : F) + x, V.subtype, fun q v => by
                simp [add_assoc]⟩
              have hg : ∀ v, g v = (v : F) + x := fun v => rfl
              have hginj : Function.Injective g := by
                intro a b h; rw [hg, hg] at h; exact Subtype.ext (add_right_cancel h)
              set S' : Set V := {v | g v ∈ S} with hS'
              have hS'c : IsCompact S' := by
                obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS.isBounded
                apply Metric.isCompact_of_isClosed_isBounded
                · exact hS.isClosed.preimage (by
                    show Continuous fun v : V => (v : F) + x
                    fun_prop)
                · rw [isBounded_iff_forall_norm_le]
                  refine ⟨R + ‖x‖, fun v hv => ?_⟩
                  have h1 := hR _ hv
                  rw [hg] at h1
                  have h2 : ‖(v : F)‖ ≤ ‖(v : F) + x‖ + ‖x‖ := by
                    calc ‖(v : F)‖ = ‖((v : F) + x) - x‖ := by rw [add_sub_cancel_right]
                      _ ≤ _ := norm_sub_le _ _
                  rw [Submodule.coe_norm] at *
                  linarith
              have hS'cv : Convex ℝ S' := hSc.affine_preimage g
              have himg : S = g '' S' := by
                ext s; constructor
                · intro hs
                  refine ⟨⟨s - x, hmemV s hs⟩, ?_, ?_⟩
                  · show g _ ∈ S; rw [hg]; simpa using hs
                  · rw [hg]; simp
                · rintro ⟨v, hv, rfl⟩; exact hv
              have hext : g '' Set.extremePoints ℝ S' ⊆ Set.extremePoints ℝ S := by
                rintro _ ⟨v, hv, rfl⟩
                rw [mem_extremePoints] at hv ⊢
                refine ⟨hv.1, ?_⟩
                intro a ha b hb hab
                rw [himg] at ha hb
                obtain ⟨a', ha', rfl⟩ := ha
                obtain ⟨b', hb', rfl⟩ := hb
                have : v ∈ openSegment ℝ a' b' := by
                  obtain ⟨s, t, hs, ht, hst, h⟩ := hab
                  refine ⟨s, t, hs, ht, hst, hginj ?_⟩
                  rw [← h, Convex.combo_affine_apply hst]
                obtain ⟨h1, h2⟩ := hv.2 a' ha' b' hb' this
                rw [h1, h2]; exact ⟨rfl, rfl⟩
              have key := ih _ hlt V rfl S' hS'c hS'cv
              have hx' : x ∈ g '' S' := himg ▸ hx
              obtain ⟨v, hv, hvx⟩ := hx'
              rw [← hvx]
              have h1 : g v ∈ g '' convexHull ℝ (Set.extremePoints ℝ S') := ⟨v, key hv, rfl⟩
              rw [AffineMap.image_convexHull] at h1
              exact convexHull_mono hext h1
            have bdry : ∀ S : Set F, IsCompact S → Convex ℝ S → (interior S).Nonempty →
                ∀ b ∈ S, b ∉ interior S → b ∈ convexHull ℝ (Set.extremePoints ℝ S) := by
              intro S hS hSc hne b hbS hb'
              obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hSc.interior isOpen_interior hb'
              have hcl : S ⊆ closure (interior S) := by
                rw [hSc.closure_interior_eq_closure_of_nonempty_interior hne, hS.isClosed.closure_eq]
              have hfle : ∀ s ∈ S, f s ≤ f b := fun s hs =>
                closure_minimal (fun a ha => (hf a ha).le)
                  (isClosed_le f.continuous continuous_const) (hcl hs)
              set Fc := S ∩ {s | f s = f b} with hFc
              have hFcc : IsCompact Fc := hS.inter_right (isClosed_eq f.continuous continuous_const)
              have hFccv : Convex ℝ Fc := by
                refine hSc.inter ?_
                intro a ha c hc s t hs ht hst
                have ha' : f a = f b := ha
                have hc' : f c = f b := hc
                show f (s • a + t • c) = f b
                rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ha', hc', ← add_mul, hst, one_mul]
              have hFcint : interior Fc = ∅ := by
                by_contra hne'
                obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hne'
                obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
                have hzF : f z = f b := (interior_subset hz).2
                have hf0 : ∀ v, f v = 0 := by
                  intro v
                  set t : ℝ := ε / (2 * (‖v‖ + 1)) with ht
                  have htpos : 0 < t := by positivity
                  have hmem : z + t • v ∈ Fc := by
                    apply hball
                    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
                      Real.norm_of_nonneg htpos.le, ht]
                    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
                    nlinarith [norm_nonneg v]
                  have e1 : f (z + t • v) = f b := hmem.2
                  rw [map_add, map_smul, hzF, smul_eq_mul] at e1
                  have : t * f v = 0 := by linarith
                  rcases mul_eq_zero.mp this with h | h
                  · exact absurd h htpos.ne'
                  · exact h
                obtain ⟨z0, hz0⟩ := hne
                have := hf z0 hz0
                rw [hf0, hf0] at this
                exact lt_irrefl _ this
              have hextF : Set.extremePoints ℝ Fc ⊆ Set.extremePoints ℝ S := by
                intro y hy
                rw [mem_extremePoints] at hy ⊢
                refine ⟨hy.1.1, ?_⟩
                intro a ha c hc hac
                have hyF : f y = f b := hy.1.2
                obtain ⟨s, t, hs, ht, hst, h⟩ := hac
                have h1 := hfle a ha
                have h2 := hfle c hc
                have h3 : s * f a + t * f c = f b := by
                  rw [← hyF, ← h, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
                have e0 : s * (f b - f a) + t * (f b - f c) = 0 := by
                  linear_combination (f b) * hst - h3
                have p1 := mul_nonneg hs.le (sub_nonneg.mpr h1)
                have p2 := mul_nonneg ht.le (sub_nonneg.mpr h2)
                have ea : f a = f b := by
                  by_contra hne
                  have := mul_pos hs (sub_pos.mpr (lt_of_le_of_ne h1 hne)); linarith
                have ec : f c = f b := by
                  by_contra hne
                  have := mul_pos ht (sub_pos.mpr (lt_of_le_of_ne h2 hne)); linarith
                exact hy.2 a ⟨ha, ea⟩ c ⟨hc, ec⟩ ⟨s, t, hs, ht, hst, h⟩
              exact convexHull_mono hextF (caseA Fc hFcc hFccv hFcint ⟨hbS, rfl⟩)
            intro S hS hSc x hx
            by_cases hint : interior S = ∅
            · exact caseA S hS hSc hint hx
            have hne : (interior S).Nonempty := Set.nonempty_iff_ne_empty.mpr hint
            obtain ⟨e, he⟩ := hS.extremePoints_nonempty ⟨x, hx⟩
            by_cases hxe : x = e
            · rw [hxe]; exact subset_convexHull ℝ _ he
            set d := x - e with hd
            have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxe)
            obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hS.isBounded
            set T : Set ℝ := {t | 1 ≤ t ∧ e + t • d ∈ S} with hT
            have hTcl : IsClosed T :=
              (isClosed_le continuous_const continuous_id).inter
                (hS.isClosed.preimage (by fun_prop))
            have h1T : (1 : ℝ) ∈ T := ⟨le_rfl, by rw [one_smul, hd, add_sub_cancel]; exact hx⟩
            have hTbdd : BddAbove T := by
              refine ⟨(R + ‖e‖) / ‖d‖, fun t ht => ?_⟩
              rw [le_div_iff₀ hdpos]
              have h1 := hR _ ht.2
              have h2 : ‖t • d‖ ≤ ‖e + t • d‖ + ‖e‖ := by
                calc ‖t • d‖ = ‖(e + t • d) - e‖ := by rw [add_sub_cancel_left]
                  _ ≤ _ := norm_sub_le _ _
              rw [norm_smul, Real.norm_of_nonneg (by linarith [ht.1])] at h2
              linarith
            have hts := hTcl.csSup_mem ⟨1, h1T⟩ hTbdd
            set ts := sSup T with htsdef
            have hts1 : 1 ≤ ts := hts.1
            set b := e + ts • d with hbdef
            have hbint : b ∉ interior S := by
              intro hb
              obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hb)
              set δ := ε / (2 * ‖d‖) with hδ
              have hδpos : 0 < δ := by positivity
              have hmem : ts + δ ∈ T := by
                refine ⟨by linarith, hball ?_⟩
                rw [Metric.mem_ball, dist_eq_norm, hbdef, add_smul, ← add_assoc, add_sub_cancel_left,
                  norm_smul, Real.norm_of_nonneg hδpos.le, hδ]
                rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
                nlinarith
              have := le_csSup hTbdd hmem
              linarith
            have hb := bdry S hS hSc hne b hts.2 hbint
            have hts0 : ts ≠ 0 := by positivity
            have hcomb := convex_convexHull ℝ (Set.extremePoints ℝ S) (subset_convexHull ℝ _ he) hb
              (a := 1 - 1 / ts) (b := 1 / ts) (by rw [sub_nonneg, div_le_one (by positivity)]; exact hts1)
              (by positivity) (by ring)
            have hx' : (1 - 1 / ts) • e + (1 / ts) • b = x := by
              rw [hbdef, smul_add, smul_smul, one_div, inv_mul_cancel₀ hts0, one_smul, hd]
              module
            rw [hx'] at hcomb
            exact hcomb
          obtain ⟨hCc, hCv, hC0⟩ := hC
          have h0C : (0 : EuclideanSpace ℝ (Fin n)) ∈ C := interior_subset hC0
          obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ C, ‖x‖ ≤ R := hCc.isBounded.exists_norm_le
          have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR 0 h0C)
          have F1 : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), ∃ x ∈ C, inner ℝ x y = 1 := by
            intro y hy
            rw [mem_extremePoints] at hy
            obtain ⟨hyP, hyext⟩ := hy
            obtain ⟨x, hx, hmax⟩ := hCc.exists_isMaxOn ⟨0, h0C⟩
              (f := fun x => inner ℝ x y) (continuous_id.inner continuous_const).continuousOn
            refine ⟨x, hx, ?_⟩
            by_contra hne
            have hlt : inner ℝ x y < 1 := lt_of_le_of_ne (hyP x hx) hne
            set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ 1 with he
            have hen : ‖e‖ = 1 := by simp [he]
            set δ : ℝ := (1 - inner ℝ x y) / (R + 1) with hδ
            have hδpos : 0 < δ := by apply div_pos <;> linarith
            have hmem : ∀ s : ℝ, |s| ≤ δ → y + s • e ∈ ConeLifts.Shared.polar C := by
              intro s hs c hc
              have h1 : inner ℝ c y ≤ inner ℝ x y := hmax hc
              have h2 : inner ℝ c (s • e) ≤ ‖c‖ * ‖s • e‖ := real_inner_le_norm _ _
              rw [norm_smul, hen, mul_one, Real.norm_eq_abs] at h2
              rw [inner_add_right]
              have h3 : ‖c‖ * |s| ≤ R * δ := mul_le_mul (hR c hc) hs (abs_nonneg _) hR0
              have h4 : R * δ < 1 - inner ℝ x y := by
                rw [hδ, mul_div_assoc']
                rw [div_lt_iff₀ (by linarith)]
                nlinarith
              linarith
            have hseg : y ∈ openSegment ℝ (y + δ • e) (y + (-δ) • e) :=
              ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by module⟩
            have := (hyext _ (hmem δ (by rw [abs_of_pos hδpos])) _ (hmem (-δ) (by
              rw [abs_neg, abs_of_pos hδpos])) hseg).1
            have h' : δ • e = 0 := add_eq_left.mp this
            have h'' := congrArg norm h'
            rw [norm_smul, hen, norm_zero, Real.norm_of_nonneg hδpos.le, mul_one] at h''
            exact hδpos.ne' h''
          have key1 : ∀ i, ConeLifts.Factorization.SlackFactorizable (𝒦.cone i) C →
              ConeLifts.Factorization.HasLift (𝒦.cone i) C := by
            intro i hsf
            obtain ⟨A, B, hAK, hBK, hAB⟩ := hsf
            have hKcv' := (𝒦.isClosedConvexCone i).2.1
            set P := ConeLifts.Shared.polar C with hP
            set Y := Set.extremePoints ℝ P with hY
            obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hC0)
            have hPcv : Convex ℝ P := by
              intro a ha b hb s t hs ht hst x hx
              rw [inner_add_right, inner_smul_right, inner_smul_right]
              have h1 := mul_le_mul_of_nonneg_left (ha x hx) hs
              have h2 := mul_le_mul_of_nonneg_left (hb x hx) ht
              linarith
            have hPcl : IsClosed P := by
              have : P = ⋂ x ∈ C, {y | inner ℝ x y ≤ 1} := by ext y; simp [hP, ConeLifts.Shared.polar]
              rw [this]
              exact isClosed_biInter fun x _ => isClosed_le (continuous_const.inner continuous_id) continuous_const
            have hPb : ∀ y ∈ P, ‖y‖ ≤ 2 / r := by
              intro y hy
              by_cases hy0 : y = 0
              · rw [hy0, norm_zero]; positivity
              have hyn : 0 < ‖y‖ := norm_pos_iff.mpr hy0
              have hmem : (r / 2 / ‖y‖) • y ∈ C := by
                apply hball
                rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity),
                  div_mul_cancel₀ _ hyn.ne']
                linarith
              have := hy _ hmem
              rw [inner_smul_left, real_inner_self_eq_norm_sq] at this
              simp only [RCLike.conj_to_real] at this
              rw [le_div_iff₀ hr]
              have e : r / 2 / ‖y‖ * ‖y‖ ^ 2 = r / 2 * ‖y‖ := by field_simp
              rw [e] at this
              linarith
            have hPc : IsCompact P := by
              apply Metric.isCompact_of_isClosed_isBounded hPcl
              rw [Metric.isBounded_iff_subset_closedBall 0]
              exact ⟨2 / r, fun y hy => by rw [Metric.mem_closedBall, dist_zero_right]; exact hPb y hy⟩
            have h0P : (0 : EuclideanSpace ℝ (Fin n)) ∈ P := fun x _ => by simp
            have KM : ∀ x t, (∀ y ∈ Y, inner ℝ x y ≤ t) → ∀ y ∈ P, inner ℝ x y ≤ t := by
              intro x t hxt
              have hcv : Convex ℝ {y : EuclideanSpace ℝ (Fin n) | inner ℝ x y ≤ t} := by
                intro a ha b hb s u hs hu hsu
                simp only [Set.mem_setOf_eq, inner_add_right, inner_smul_right] at *
                have h1 := mul_le_mul_of_nonneg_left ha hs
                have h2 := mul_le_mul_of_nonneg_left hb hu
                have h3 : s * t + u * t = t := by rw [← add_mul, hsu, one_mul]
                linarith
              have h1 : convexHull ℝ Y ⊆ {y | inner ℝ x y ≤ t} := convexHull_min hxt hcv
              have h2 : closure (convexHull ℝ Y) ⊆ {y | inner ℝ x y ≤ t} :=
                closure_minimal h1 (isClosed_le (continuous_const.inner continuous_id) continuous_const)
              rw [hY, closure_convexHull_extremePoints hPc hPcv] at h2
              exact h2
            have bipolar : ∀ x, (∀ y ∈ P, inner ℝ x y ≤ 1) → x ∈ C := by
              intro x hx
              by_contra hxC
              obtain ⟨f, u, hfC, hfx⟩ := geometric_hahn_banach_closed_point hCv hCc.isClosed hxC
              have hu : 0 < u := by simpa using hfC 0 h0C
              set y := (InnerProductSpace.toDual ℝ _).symm (u⁻¹ • f) with hy
              have hyf : ∀ v, inner ℝ v y = u⁻¹ * f v := by
                intro v; rw [hy, real_inner_comm, InnerProductSpace.toDual_symm_apply]; rfl
              have hyP : y ∈ P := by
                intro c hc; rw [hyf]
                have := hfC c hc
                rw [inv_mul_le_iff₀ hu]; linarith
              have := hx y hyP
              rw [hyf, inv_mul_le_iff₀ hu] at this
              linarith
            have span0 : ∀ x t, (∀ y ∈ Y, t - inner ℝ x y = 0) → t = 0 ∧ x = 0 := by
              intro x t h
              have h1 := KM x t (fun y hy => by linarith [h y hy])
              have h2 := KM (-x) (-t) (fun y hy => by rw [inner_neg_left]; linarith [h y hy])
              have hP' : ∀ y ∈ P, inner ℝ x y = t := by
                intro y hy; have := h1 y hy; have := h2 y hy; rw [inner_neg_left] at this; linarith
              have ht : t = 0 := by have := hP' 0 h0P; simp at this; linarith
              refine ⟨ht, ?_⟩
              set c : ℝ := 1 / ((R + 1) * (‖x‖ + 1)) with hc
              have hcpos : 0 < c := by positivity
              have hcx : c • x ∈ P := by
                intro v hv
                have h3 : inner ℝ v (c • x) ≤ ‖v‖ * ‖c • x‖ := real_inner_le_norm _ _
                rw [norm_smul, Real.norm_of_nonneg hcpos.le] at h3
                have h4 : ‖v‖ * (c * ‖x‖) ≤ R * (c * ‖x‖) :=
                  mul_le_mul_of_nonneg_right (hR v hv) (by positivity)
                have h5 : R * (c * ‖x‖) < 1 := by
                  rw [hc]
                  rw [show R * (1 / ((R + 1) * (‖x‖ + 1)) * ‖x‖) = (R * ‖x‖) / ((R + 1) * (‖x‖ + 1)) by ring]
                  rw [div_lt_one (by positivity)]
                  nlinarith [norm_nonneg x]
                linarith
              have := hP' _ hcx
              rw [inner_smul_right, real_inner_self_eq_norm_sq, ht] at this
              have : ‖x‖ ^ 2 = 0 := by
                rcases mul_eq_zero.mp this with h | h
                · exact absurd h hcpos.ne'
                · exact h
              simpa using this
            have Mink : C ⊆ convexHull ℝ (Set.extremePoints ℝ C) :=
              Mk _ (EuclideanSpace ℝ (Fin n)) rfl C hCc hCv
            let S : Submodule ℝ (EuclideanSpace ℝ (Fin (𝒦.dim i)) × ℝ × EuclideanSpace ℝ (Fin n)) :=
              { carrier := {p | ∀ y ∈ Y, p.2.1 - inner ℝ p.2.2 y = inner ℝ p.1 (B y)}
                add_mem' := by
                  intro a b ha hb y hy
                  simp only [Prod.fst_add, Prod.snd_add, inner_add_left]
                  have := ha y hy; have := hb y hy; linarith
                zero_mem' := by intro y hy; simp
                smul_mem' := by
                  intro c a ha y hy
                  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, inner_smul_left, RCLike.conj_to_real]
                  have := ha y hy; rw [← this]; ring }
            let p := (LinearMap.fst ℝ _ (ℝ × EuclideanSpace ℝ (Fin n))).comp S.subtype
            have hker : LinearMap.ker p = ⊥ := by
              rw [LinearMap.ker_eq_bot']
              intro m hm
              have hm1 : m.1.1 = 0 := hm
              have hmem : ∀ y ∈ Y, m.1.2.1 - inner ℝ m.1.2.2 y = inner ℝ m.1.1 (B y) := m.2
              have := span0 m.1.2.2 m.1.2.1 (fun y hy => by rw [hmem y hy, hm1, inner_zero_left])
              apply Subtype.ext
              show m.1 = (0, 0, 0)
              ext1
              · exact hm1
              · ext1
                · exact this.1
                · exact this.2
            obtain ⟨q, hq⟩ := LinearMap.exists_leftInverse_of_injective p hker
            let π := (LinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n))).comp
              ((LinearMap.snd ℝ (EuclideanSpace ℝ (Fin (𝒦.dim i))) _).comp (S.subtype.comp q))
            have hπ : ∀ z x, (∀ y ∈ Y, 1 - inner ℝ x y = inner ℝ z (B y)) → π z = x := by
              intro z x h
              have hm : (z, (1 : ℝ), x) ∈ S := h
              have h1 : q (p ⟨_, hm⟩) = ⟨_, hm⟩ := by rw [← LinearMap.comp_apply, hq]; rfl
              have h2 : p ⟨_, hm⟩ = z := rfl
              rw [h2] at h1
              show (q z).1.2.2 = x
              rw [h1]
            let L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (𝒦.dim i))) :=
              { carrier := {z | ∃ x, ∀ y ∈ Y, 1 - inner ℝ x y = inner ℝ z (B y)}
                smul_vsub_vadd_mem' := by
                  rintro c p1 p2 p3 ⟨x1, h1⟩ ⟨x2, h2⟩ ⟨x3, h3⟩
                  refine ⟨c • (x1 - x2) + x3, fun y hy => ?_⟩
                  rw [vsub_eq_sub, vadd_eq_add, inner_add_left, inner_smul_left, inner_sub_left,
                    inner_add_left, inner_smul_left, inner_sub_left, ← h1 y hy, ← h2 y hy, ← h3 y hy]
                  simp only [RCLike.conj_to_real]; ring }
            refine ⟨L, π, ?_⟩
            apply Set.Subset.antisymm
            · refine Mink.trans (convexHull_min ?_ ((hKcv'.inter L.convex).linear_image π))
              intro x hx
              exact ⟨A x, ⟨hAK x hx, ⟨x, hAB x hx⟩⟩, hπ _ _ (hAB x hx)⟩
            · rintro _ ⟨z, ⟨hzK, x, hx⟩, rfl⟩
              rw [hπ z x hx]
              apply bipolar
              apply KM
              intro y hy
              have := hBK y hy z hzK
              have := hx y hy
              linarith
          have proper : ∀ i (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (𝒦.dim i))))
              (π : EuclideanSpace ℝ (Fin (𝒦.dim i)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
              C = π '' (𝒦.cone i ∩ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))))) → (interior (𝒦.cone i) ∩ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))))).Nonempty →
              ConeLifts.Factorization.SlackFactorizable (𝒦.cone i) C := by
            intro i L π hL hp
            obtain ⟨hKcl, hKcv, hK0, hKsm⟩ := 𝒦.isClosedConvexCone i
            have hKint := 𝒦.interior_nonempty i
            obtain ⟨z0, hz0K, hz0L⟩ := hp
            have hmemC : ∀ x ∈ C, ∃ z, z ∈ 𝒦.cone i ∧ z ∈ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i)))) ∧ π z = x := by
              intro x hx
              rw [hL] at hx
              obtain ⟨z, ⟨h1, h2⟩, h3⟩ := hx
              exact ⟨z, h1, h2, h3⟩
            have hcl : 𝒦.cone i ⊆ closure (interior (𝒦.cone i)) := by
              rw [hKcv.closure_interior_eq_closure_of_nonempty_interior hKint, hKcl.closure_eq]
            have hLmem : ∀ c : ℝ, ∀ p q r, p ∈ L → q ∈ L → r ∈ L → c • (p - q) + r ∈ L :=
              fun c p q r hp hq hr => L.smul_vsub_vadd_mem c hp hq hr
            have hB : ∀ y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C), ∃ b,
                b ∈ ConeLifts.Shared.dualCone (𝒦.cone i) ∧ ∀ z ∈ L, inner ℝ z b = 1 - inner ℝ (π z) y := by
              intro y hy
              have hyP : y ∈ ConeLifts.Shared.polar C := hy.1
              obtain ⟨x1, hx1, hx1y⟩ := F1 y hy
              obtain ⟨z1, hz1K, hz1L, hz1π⟩ := hmemC x1 hx1
              obtain ⟨z2, hz2K, hz2L, hz2π⟩ := hmemC 0 h0C
              set lam : EuclideanSpace ℝ (Fin (𝒦.dim i)) → ℝ := fun z => inner ℝ (π z) y with hlam
              have lam_add : ∀ a b, lam (a + b) = lam a + lam b := by
                intro a b; simp [hlam, map_add, inner_add_left]
              have lam_smul : ∀ (c : ℝ) a, lam (c • a) = c * lam a := by
                intro c a; simp [hlam, map_smul, inner_smul_left]
              have lam_sub : ∀ a b, lam (a - b) = lam a - lam b := by
                intro a b; simp [hlam, map_sub, inner_sub_left]
              have hl1 : lam z1 = 1 := by simp [hlam, hz1π, hx1y]
              have hl2 : lam z2 = 0 := by simp [hlam, hz2π]
              set U : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))) := (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i)))) ∩ {z | 1 < lam z} with hU
              have hUcv : Convex ℝ U := by
                refine L.convex.inter ?_
                intro a ha b hb s t hs ht hst
                show 1 < lam (s • a + t • b)
                rw [lam_add, lam_smul, lam_smul]
                have ha' : 1 < lam a := ha
                have hb' : 1 < lam b := hb
                rcases hs.lt_or_eq with hs' | hs'
                · have := mul_lt_mul_of_pos_left ha' hs'
                  have := mul_le_mul_of_nonneg_left hb'.le ht
                  linarith
                · subst hs'; simp at hst; subst hst; simpa using hb'
              have hdisj : Disjoint (interior (𝒦.cone i)) U := by
                rw [Set.disjoint_left]
                rintro z hzK ⟨hzL, hz1⟩
                have : π z ∈ C := by rw [hL]; exact ⟨z, ⟨interior_subset hzK, hzL⟩, rfl⟩
                have := hyP _ this
                have h' : 1 < lam z := hz1
                simp only [hlam] at h'
                linarith
              obtain ⟨f, u, hfK, hfU⟩ := geometric_hahn_banach_open hKcv.interior isOpen_interior hUcv hdisj
              have hfu : ∀ k ∈ 𝒦.cone i, f k ≤ u := by
                intro k hk
                have : closure (interior (𝒦.cone i)) ⊆ {x | f x ≤ u} :=
                  closure_minimal (fun a ha => (hfK a ha).le) (isClosed_le f.continuous continuous_const)
                exact this (hcl hk)
              have hu0 : 0 ≤ u := by simpa using hfu 0 hK0
              have hfK0 : ∀ k ∈ 𝒦.cone i, f k ≤ 0 := by
                intro k hk
                by_contra h
                push Not at h
                have := hfu (((u + 1) / f k) • k) (hKsm _ (by positivity) k hk)
                rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne'] at this
                linarith
              set w := z1 - z2 with hw
              have hlw : lam w = 1 := by rw [hw, lam_sub, hl1, hl2]; ring
              -- the main inequality
              have hmain : ∀ z ∈ L, ∀ s t : ℝ, 0 < s →
                  0 ≤ f z1 + s * f w + t * (f z - f z1 - (lam z - 1) * f w) := by
                intro z hz s t hs
                have hq1 : (s - t * (lam z - 1)) • (z1 - z2) + z1 ∈ L := hLmem _ _ _ _ hz1L hz2L hz1L
                have hp : t • (z - z1) + ((s - t * (lam z - 1)) • (z1 - z2) + z1) ∈ L :=
                  hLmem _ _ _ _ hz hz1L hq1
                have hpU : t • (z - z1) + ((s - t * (lam z - 1)) • (z1 - z2) + z1) ∈ U := by
                  refine ⟨hp, ?_⟩
                  show 1 < lam _
                  rw [lam_add, lam_smul, lam_sub, lam_add, lam_smul, ← hw, hlw, hl1]
                  linarith
                have := le_trans hu0 (hfU _ hpU)
                rw [map_add, map_smul, map_sub, map_add, map_smul, ← hw, smul_eq_mul, smul_eq_mul] at this
                linarith
              have hd : ∀ z ∈ L, f z - f z1 - (lam z - 1) * f w = 0 := by
                intro z hz
                by_contra hne
                have := hmain z hz 1 (-(f z1 + 1 * f w + 1) / (f z - f z1 - (lam z - 1) * f w)) one_pos
                rw [div_mul_cancel₀ _ hne] at this
                linarith
              have hfz1 : f z1 = 0 := by
                refine le_antisymm (hfK0 z1 hz1K) ?_
                by_contra hneg
                push Not at hneg
                set s : ℝ := -f z1 / (2 * (|f w| + 1)) with hs
                have hspos : 0 < s := by apply div_pos (by linarith); positivity
                have h1 := hmain z1 hz1L s 0 hspos
                have h2 : s * |f w| < -f z1 := by
                  rw [hs, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
                  have : 0 < -f z1 := by linarith
                  linarith [mul_nonneg this.le (abs_nonneg (f w))]
                have h3 : s * f w ≤ s * |f w| := mul_le_mul_of_nonneg_left (le_abs_self _) hspos.le
                simp only [zero_mul, add_zero] at h1
                linarith
              have hfz : ∀ z ∈ L, f z = (lam z - 1) * f w := by
                intro z hz; have := hd z hz; rw [hfz1] at this; linarith
              have hfw : 0 < f w := by
                have hz1w : (1 : ℝ) • (z1 - z2) + z1 ∈ L := hLmem _ _ _ _ hz1L hz2L hz1L
                have hU1 : (1 : ℝ) • (z1 - z2) + z1 ∈ U := by
                  refine ⟨hz1w, ?_⟩
                  show 1 < lam _
                  rw [lam_add, lam_smul, ← hw, hlw, hl1]; norm_num
                have e1 := hfU _ hU1
                rw [hfz _ hz1w, lam_add, lam_smul, ← hw, hlw, hl1] at e1
                have e2 := hfK z0 hz0K
                rw [hfz _ hz0L] at e2
                by_contra hle
                push Not at hle
                have hw0 : f w = 0 := le_antisymm hle (by linarith)
                rw [hw0] at e1 e2
                linarith
              refine ⟨(InnerProductSpace.toDual ℝ _).symm (-(f w)⁻¹ • f), ?_, ?_⟩
              · intro k hk
                rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
                simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
                have hk0 := hfK0 k hk
                have hwi : 0 < (f w)⁻¹ := inv_pos.mpr hfw
                linarith [mul_nonneg hwi.le (neg_nonneg.mpr hk0)]
              · intro z hz
                rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
                simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
                rw [hfz z hz]
                have : lam z = inner ℝ (π z) y := rfl
                rw [← this]
                field_simp
                ring
            have hA : ∀ x, ∃ z, x ∈ C → z ∈ 𝒦.cone i ∧ z ∈ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i)))) ∧ π z = x := by
              intro x
              by_cases hx : x ∈ C
              · obtain ⟨z, hz⟩ := hmemC x hx; exact ⟨z, fun _ => hz⟩
              · exact ⟨0, fun h => absurd h hx⟩
            have hB' : ∀ y, ∃ b, y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C) →
                b ∈ ConeLifts.Shared.dualCone (𝒦.cone i) ∧ ∀ z ∈ L, inner ℝ z b = 1 - inner ℝ (π z) y := by
              intro y
              by_cases hy : y ∈ Set.extremePoints ℝ (ConeLifts.Shared.polar C)
              · obtain ⟨b, hb⟩ := hB y hy; exact ⟨b, fun _ => hb⟩
              · exact ⟨0, fun h => absurd h hy⟩
            choose A hA using hA
            choose B hB'' using hB'
            refine ⟨A, B, fun x hx => (hA x hx.1).1,
              fun y hy => (hB'' y hy).1, ?_⟩
            intro x hx y hy
            obtain ⟨-, hAL, hAπ⟩ := hA x hx.1
            rw [(hB'' y hy).2 _ hAL, hAπ]
          have reduce : ∀ i (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (𝒦.dim i))))
              (π : EuclideanSpace ℝ (Fin (𝒦.dim i)) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)),
              C = π '' (𝒦.cone i ∩ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))))) → ¬ (interior (𝒦.cone i) ∩ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))))).Nonempty →
              ∃ j < i, ConeLifts.Factorization.HasLift (𝒦.cone j) C := by
            intro i L π hL hp
            obtain ⟨hKcl, hKcv, hK0, hKsm⟩ := 𝒦.isClosedConvexCone i
            have hKint := 𝒦.interior_nonempty i
            have h0C : (0 : EuclideanSpace ℝ (Fin n)) ∈ C := interior_subset hC0
            obtain ⟨zL, hzL, -⟩ : (0 : EuclideanSpace ℝ (Fin n)) ∈ π '' (𝒦.cone i ∩ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))))) := hL ▸ h0C
            have hdisj : Disjoint (interior (𝒦.cone i)) (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i)))) :=
              Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hp)
            obtain ⟨f, u, hfK, hfL⟩ := geometric_hahn_banach_open hKcv.interior isOpen_interior
              L.convex hdisj
            have hcl : 𝒦.cone i ⊆ closure (interior (𝒦.cone i)) := by
              rw [hKcv.closure_interior_eq_closure_of_nonempty_interior hKint, hKcl.closure_eq]
            have hfu : ∀ k ∈ 𝒦.cone i, f k ≤ u := by
              intro k hk
              have : closure (interior (𝒦.cone i)) ⊆ {x | f x ≤ u} :=
                closure_minimal (fun a ha => (hfK a ha).le) (isClosed_le f.continuous continuous_const)
              exact this (hcl hk)
            have hu0 : 0 ≤ u := by simpa using hfu 0 hK0
            have hfK0 : ∀ k ∈ 𝒦.cone i, f k ≤ 0 := by
              intro k hk
              by_contra h
              push Not at h
              have := hfu (((u + 1) / f k) • k) (hKsm _ (by positivity) k hk)
              rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ h.ne'] at this
              linarith
            have hKLf : ∀ z ∈ 𝒦.cone i, z ∈ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i)))) → f z = 0 := by
              intro z hz hzl
              have := hfL z hzl
              have := hfK0 z hz
              linarith
            obtain ⟨j, hji, T, hTinj, hTF⟩ := h𝒦 i (𝒦.cone i ∩ {z | f z = 0}) ⟨0, hK0, by simp⟩
              (by
                intro x hx y hy a b ha hb hab
                refine ⟨hKcv hx.1 hy.1 ha hb hab, ?_⟩
                have h1 : f x = 0 := hx.2
                have h2 : f y = 0 := hy.2
                show f (a • x + b • y) = 0
                rw [map_add, map_smul, map_smul, h1, h2]; simp)
              (by
                refine ⟨Set.inter_subset_left, ?_⟩
                intro x1 hx1 x2 hx2 x hx hseg
                obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
                have hx' : f (a • x1 + b • x2) = 0 := hx.2
                rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hx'
                have h1 := hfK0 x1 hx1
                have h2 := hfK0 x2 hx2
                have q1 := mul_nonpos_of_nonneg_of_nonpos ha.le h1
                have q2 := mul_nonpos_of_nonneg_of_nonpos hb.le h2
                have e1 : f x1 = 0 := (mul_eq_zero.mp (by linarith : a * f x1 = 0)).resolve_left ha.ne'
                exact ⟨hx1, e1⟩)
            have hji' : j < i := by
              refine lt_of_le_of_ne hji ?_
              rintro rfl
              have hsurj : Function.Surjective T := LinearMap.injective_iff_surjective.mp hTinj
              have hg : ∀ k ∈ 𝒦.cone j, f (T k) = 0 := by
                intro k hk
                have : T k ∈ T '' 𝒦.cone j := ⟨k, hk, rfl⟩
                rw [hTF] at this
                exact this.2
              obtain ⟨z0, hz0⟩ := hKint
              obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz0)
              have hg0 : ∀ v, f (T v) = 0 := by
                intro v
                set t : ℝ := ε / (2 * (‖v‖ + 1)) with ht
                have htpos : 0 < t := by positivity
                have hmem : z0 + t • v ∈ 𝒦.cone j := by
                  apply hball
                  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
                    Real.norm_of_nonneg htpos.le, ht]
                  have : ‖v‖ < ‖v‖ + 1 := by linarith
                  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
                  nlinarith [norm_nonneg v]
                have e1 := hg _ hmem
                have e2 := hg z0 (interior_subset hz0)
                rw [map_add, map_smul, map_add, map_smul, e2, zero_add, smul_eq_mul] at e1
                rcases mul_eq_zero.mp e1 with h | h
                · exact absurd h htpos.ne'
                · exact h
              have hf0 : ∀ w, f w = 0 := fun w => by
                obtain ⟨v, rfl⟩ := hsurj w
                exact hg0 v
              have := hfL zL hzL.2
              have := hfK z0 hz0
              rw [hf0] at *
              linarith
            refine ⟨j, hji', L.comap T.toAffineMap, π ∘ₗ T, ?_⟩
            rw [AffineSubspace.coe_comap, LinearMap.coe_comp, Set.image_comp]
            rw [LinearMap.coe_toAffineMap, Set.image_inter_preimage, hTF, hL]
            congr 1
            ext z
            constructor
            · rintro ⟨hz, hzl⟩; exact ⟨⟨hz, hKLf z hz hzl⟩, hzl⟩
            · rintro ⟨⟨hz, -⟩, hzl⟩; exact ⟨hz, hzl⟩
          have key2 : ∀ i, ConeLifts.Factorization.HasLift (𝒦.cone i) C →
              ∃ j ≤ i, ConeLifts.Factorization.SlackFactorizable (𝒦.cone j) C := by
            intro i
            induction i using Nat.strong_induction_on with
            | _ i ih =>
              rintro ⟨L, π, hL⟩
              by_cases hp : (interior (𝒦.cone i) ∩ (L : Set (EuclideanSpace ℝ (Fin (𝒦.dim i))))).Nonempty
              · exact ⟨i, le_rfl, proper i L π hL hp⟩
              · obtain ⟨j, hji, hj⟩ := reduce i L π hL hp
                obtain ⟨k, hkj, hk⟩ := ih j hji hj
                exact ⟨k, hkj.trans hji.le, hk⟩
          apply le_antisymm
          · apply le_iInf₂; intro i hi
            obtain ⟨j, hj, hsf⟩ := key2 i hi
            exact (iInf₂_le j hsf).trans (by exact_mod_cast hj)
          · apply le_iInf₂; intro i hi
            exact iInf₂_le i (key1 i hi)
