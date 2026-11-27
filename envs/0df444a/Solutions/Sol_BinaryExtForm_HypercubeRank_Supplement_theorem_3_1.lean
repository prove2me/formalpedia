-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.Supplement.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:38.783252+00:00
-- url     : https://prove2.me/submissions/e537d9cb-12ed-49f4-9e92-caa623257f8f

import Mathlib
import Definitions.Def_BinaryExtForm_HypercubeRank_Model
import Definitions.Def_BinaryExtForm_HypercubeRank_Supplement_Formulation

open BinaryExtForm
open BinaryExtForm.HypercubeRank
open BinaryExtForm.HypercubeRank.Supplement

open BinaryExtForm.HypercubeRank
theorem solution {n p d k : ℕ} (hpn : p ≤ n) (P : Set (Fin n → ℝ)) (hP : IsPolytope P)
    (hPk : ∀ x ∈ P, ∀ i : Fin p, 0 ≤ xc hpn x i ∧ xc hpn x i ≤ k)
    (B : Fin p → Set (Fin (d + 1) → ℝ)) (hB : ∀ i, IsBinarization d k (B i))
    (hN : ∀ i, IsNatural (B i))
    (xbar : Fin n → ℝ) (ybar : Fin p → Fin d → ℝ) (hy : ∀ i j, 0 ≤ ybar i j ∧ ybar i j ≤ 1) :
    (xbar, ybar) ∈ Set.extremePoints ℝ (BEF hpn P B) ↔
      ∃ (I : Finset (Fin p)) (α : Fin p → ℕ) (F : Set (Fin n → ℝ)),
        (∀ i ∈ I, α i ≤ k) ∧ IsFace P F ∧ affDim F = I.card ∧
        F ∩ G hpn I α = {xbar} ∧
        (∀ i ∈ I, block hpn (xbar, ybar) i ∈ Set.extremePoints ℝ (B i)) ∧
        (∀ i ∉ I, block hpn (xbar, ybar) i ∈
          Set.extremePoints ℝ (slice (B i) (xc hpn xbar i))) := by
            classical
            have hPc : Convex ℝ P := by obtain ⟨S, rfl⟩ := hP; exact convex_convexHull ℝ _
            have hBc : ∀ i, Convex ℝ (B i) := fun i => by
              obtain ⟨S, hS⟩ := (hB i).1; rw [hS]; exact convex_convexHull ℝ _
            have L1 : ∀ {m : ℕ} (C : Set (Fin m → ℝ)), Convex ℝ C → ∀ x ∈ C, ∀ a ∈ C, ∀ s : ℝ, 0 < s →
                x - s • (a - x) ∈ C → ∀ᶠ t in nhds (0:ℝ), x + t • (a - x) ∈ C := by
              intro m C hC x hx a ha s hs hxs
              filter_upwards [Icc_mem_nhds (neg_lt_zero.2 hs) one_pos] with t ht
              rcases le_total 0 t with h | h
              · exact hC.add_smul_sub_mem hx ha ⟨h, ht.2⟩
              · have := hC.add_smul_sub_mem hx hxs (t := -t / s)
                  ⟨div_nonneg (by linarith) hs.le, (div_le_one hs).2 (by linarith [ht.1])⟩
                convert this using 1
                rw [show (x - s • (a - x)) - x = (-s) • (a - x) by module, smul_smul]
                congr 2; field_simp
            have L2 : ∀ {m : ℕ} (C : Set (Fin m → ℝ)), Convex ℝ C → ∀ x, ∀ a ∈ C, ∀ c ∈ C,
                x ∈ openSegment ℝ a c → ∀ᶠ t in nhds (0:ℝ), x + t • (a - x) ∈ C := by
              intro m C hC x a ha c hc hseg
              obtain ⟨μ, ν, hμ, hν, hμν, rfl⟩ := hseg
              have hx : μ • a + ν • c ∈ C := hC ha hc hμ.le hν.le hμν
              obtain rfl : ν = 1 - μ := by linarith
              refine L1 C hC _ hx a ha μ hμ ?_
              have := hC ha hc (mul_nonneg hμ.le hμ.le) (mul_nonneg hν.le (by linarith : (0:ℝ) ≤ 1 + μ))
                (by ring)
              convert this using 1
              module
            have hsegblk : ∀ z1 z2 z : Pt n p d, z ∈ openSegment ℝ z1 z2 → ∀ i,
                block hpn z i ∈ openSegment ℝ (block hpn z1 i) (block hpn z2 i) := by
              rintro z1 z2 z ⟨a, b, ha, hb, hab, rfl⟩ i
              refine ⟨a, b, ha, hb, hab, ?_⟩
              funext m
              refine Fin.cases ?_ (fun j => ?_) m <;> simp [block, xc]
            constructor
            swap
            · rintro ⟨I, α, F, hαk, hF, -, hFG, hI, hnI⟩
              have hxFG : xbar ∈ F ∩ G hpn I α := by rw [hFG]; rfl
              refine ⟨⟨hF.2.1 hxFG.1, hy, fun i => ?_⟩, ?_⟩
              · by_cases hi : i ∈ I
                · exact (hI i hi).1
                · exact (hnI i hi).1.1
              · intro z1 h1 z2 h2 hseg
                obtain ⟨x1, y1⟩ := z1
                have hb := hsegblk _ _ _ hseg
                have hxseg : xbar ∈ openSegment ℝ x1 z2.1 := by
                  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
                  exact ⟨a, b, ha, hb, hab, congrArg Prod.fst heq⟩
                have hx1F : x1 ∈ F := hF.2.left_mem_of_mem_openSegment h1.1 h2.1 hxFG.1 hxseg
                have hx1G : x1 ∈ G hpn I α := by
                  intro i hi
                  have := congrFun ((hI i hi).2 (h1.2.2 i) (h2.2.2 i) (hb i)) 0
                  simp [block] at this
                  rw [this]; exact hxFG.2 i hi
                have hx1 : x1 = xbar := by
                  have : x1 ∈ F ∩ G hpn I α := ⟨hx1F, hx1G⟩
                  rw [hFG] at this; exact this
                have hx2F : z2.1 ∈ F := hF.2.left_mem_of_mem_openSegment h2.1 h1.1 hxFG.1
                  (openSegment_symm ℝ x1 z2.1 ▸ hxseg)
                have hx2G : z2.1 ∈ G hpn I α := by
                  intro i hi
                  have := congrFun ((hI i hi).2 (h2.2.2 i) (h1.2.2 i)
                    (openSegment_symm ℝ (block hpn (x1, y1) i) (block hpn z2 i) ▸ hb i)) 0
                  simp [block] at this
                  rw [this]; exact hxFG.2 i hi
                have hx2 : z2.1 = xbar := by
                  have : z2.1 ∈ F ∩ G hpn I α := ⟨hx2F, hx2G⟩
                  rw [hFG] at this; exact this
                subst hx1
                have hblk : ∀ i, block hpn (x1, y1) i = block hpn (x1, ybar) i := by
                  intro i
                  by_cases hi : i ∈ I
                  · exact (hI i hi).2 (h1.2.2 i) (h2.2.2 i) (hb i)
                  · exact (hnI i hi).2 ⟨h1.2.2 i, by simp [block]⟩ ⟨h2.2.2 i, by simp [block, hx2]⟩ (hb i)
                refine Prod.ext rfl ?_
                funext i j
                have := congrFun (hblk i) j.succ
                simpa [block] using this
            · intro hext
              have hQ := hext.1
              have hxP : xbar ∈ P := hQ.1
              have hslice : ∀ i, block hpn (xbar, ybar) i ∈
                  Set.extremePoints ℝ (slice (B i) (xc hpn xbar i)) := by
                intro i
                refine ⟨⟨hQ.2.2 i, by simp [block]⟩, ?_⟩
                intro b1 hb1 b2 hb2 hseg
                have mk : ∀ b ∈ slice (B i) (xc hpn xbar i),
                    ((xbar, Function.update ybar i (Fin.tail b)) : Pt n p d) ∈ BEF hpn P B := by
                  intro b hb
                  refine ⟨hxP, fun i' j => ?_, fun i' => ?_⟩
                  · by_cases h : i' = i
                    · subst h; simp [Fin.tail]; exact (hB i').2.2.1 b hb.1 j
                    · simp [h]; exact hy i' j
                  · by_cases h : i' = i
                    · subst h; convert hb.1 using 1; funext m
                      refine Fin.cases ?_ (fun j => ?_) m
                      · simp [block, hb.2]
                      · simp [block, Fin.tail]
                    · convert hQ.2.2 i' using 1; funext m
                      refine Fin.cases ?_ (fun j => ?_) m <;> simp [block, h]
                obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
                have hz : (xbar, ybar) ∈ openSegment ℝ ((xbar, Function.update ybar i (Fin.tail b1)) : Pt n p d)
                    (xbar, Function.update ybar i (Fin.tail b2)) := by
                  refine ⟨a, b, ha, hb, hab, Prod.ext ?_ ?_⟩
                  · simp [← add_smul, hab]
                  · funext i' j
                    by_cases h : i' = i
                    · subst h
                      have := congrFun heq j.succ
                      simpa [block, Fin.tail] using this
                    · simp [h, ← add_mul, hab]
                have h1 := hext.2 (mk b1 hb1) (mk b2 hb2) hz
                have h2 := congrArg (fun z => z.2 i) h1
                simp only [Function.update_self] at h2
                funext m
                refine Fin.cases ?_ (fun j => ?_) m
                · simp [block, hb1.2]
                · have := congrFun h2 j
                  simpa [block, Fin.tail] using this
              set J : Finset (Fin p) := Finset.univ.filter
                (fun i => block hpn (xbar, ybar) i ∈ Set.extremePoints ℝ (B i)) with hJ
              have hint : ∀ i ∈ J, xc hpn xbar i = (⌊xc hpn xbar i⌋₊ : ℝ) ∧ ⌊xc hpn xbar i⌋₊ ≤ k := by
                intro i hi
                have hv := (Finset.mem_filter.1 hi).2
                obtain ⟨m, hm⟩ := hN i _ hv
                have h0 : block hpn (xbar, ybar) i 0 = xc hpn xbar i := by simp [block]
                rw [h0] at hm
                obtain ⟨h1, h2⟩ := hPk xbar hxP i
                have hm0 : 0 ≤ m := by
                  have : (0:ℝ) ≤ m := hm ▸ h1
                  exact_mod_cast this
                lift m to ℕ using hm0
                have hm' : xc hpn xbar i = (m : ℝ) := by simpa using hm
                rw [hm', Nat.floor_natCast]
                exact ⟨rfl, by exact_mod_cast (hm' ▸ h2)⟩
              have h2t : ∀ c : ℝ, Filter.Tendsto (fun t : ℝ => t * c) (nhds 0) (nhds 0) := fun c => by
                exact (continuous_mul_const c).tendsto' (0:ℝ) 0 (by simp)
              let D : Submodule ℝ (Fin n → ℝ) :=
                { carrier := {v | ∀ᶠ t in nhds (0:ℝ), xbar + t • v ∈ P}
                  add_mem' := by
                    intro v w hv hw
                    filter_upwards [(h2t 2).eventually hv, (h2t 2).eventually hw] with t h1 h2'
                    have := hPc h1 h2' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
                    convert this using 1
                    module
                  zero_mem' := by
                    simp only [Set.mem_ofPred_eq, smul_zero, add_zero]
                    exact Filter.Eventually.of_forall (fun _ => hxP)
                  smul_mem' := by
                    intro c v hv
                    filter_upwards [(h2t c).eventually hv] with t ht
                    simpa [smul_smul] using ht }
              have hDmem : ∀ v, v ∈ D ↔ ∀ᶠ t in nhds (0:ℝ), xbar + t • v ∈ P := fun v => Iff.rfl
              have hkey : ∀ v ∈ D, (∀ i ∈ J, xc hpn v i = 0) → v = 0 := by
                intro v hv hvJ
                have hU : ∀ i, ∃ u : Fin (d+1) → ℝ, u 0 = xc hpn v i ∧
                    ∀ᶠ t in nhds (0:ℝ), block hpn (xbar, ybar) i + t • u ∈ B i := by
                  intro i
                  by_cases hi : i ∈ J
                  · exact ⟨0, by simp [hvJ i hi], Filter.Eventually.of_forall (fun t => by simpa using hQ.2.2 i)⟩
                  · have hne : block hpn (xbar, ybar) i ∉ Set.extremePoints ℝ (B i) := fun h =>
                      hi (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
                    rw [mem_extremePoints_iff_left] at hne
                    push Not at hne
                    obtain ⟨b1, hb1, b2, hb2, hseg, hne'⟩ := hne (hQ.2.2 i)
                    have h10 : b1 0 ≠ xc hpn xbar i := by
                      intro h10
                      obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
                      have e0 := congrFun heq 0
                      simp [block] at e0
                      have h20 : b2 0 = xc hpn xbar i := by
                        rw [h10] at e0
                        have : b * b2 0 = b * xc hpn xbar i := by
                          have : a = 1 - b := by linarith
                          subst this; linarith
                        exact mul_left_cancel₀ hb.ne' this
                      exact hne' ((hslice i).2 ⟨hb1, h10⟩ ⟨hb2, h20⟩ ⟨a, b, ha, hb, hab, heq⟩)
                    have hev := L2 (B i) (hBc i) _ b1 hb1 b2 hb2 hseg
                    have h0 : block hpn (xbar, ybar) i 0 = xc hpn xbar i := by simp [block]
                    refine ⟨(xc hpn v i / (b1 0 - xc hpn xbar i)) • (b1 - block hpn (xbar, ybar) i), ?_, ?_⟩
                    · simp only [Pi.smul_apply, Pi.sub_apply, h0, smul_eq_mul]
                      field_simp [sub_ne_zero.2 h10]
                    · filter_upwards [(h2t (xc hpn v i / (b1 0 - xc hpn xbar i))).eventually hev] with t ht
                      simpa [smul_smul] using ht
                choose U hU0 hUev using hU
                have hall : ∀ᶠ t in nhds (0:ℝ), xbar + t • v ∈ P ∧
                    ∀ i, block hpn (xbar, ybar) i + t • U i ∈ B i :=
                  ((hDmem v).1 hv).and (Filter.eventually_all.2 hUev)
                obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 hall
                have mem : ∀ t : ℝ, |t| < ε →
                    ((xbar + t • v, fun i j => ybar i j + t * U i j.succ) : Pt n p d) ∈ BEF hpn P B := by
                  intro t ht
                  have h := hεP (show dist t 0 < ε by simpa using ht)
                  have hblk : ∀ i, block hpn ((xbar + t • v, fun i j => ybar i j + t * U i j.succ) : Pt n p d) i
                      = block hpn (xbar, ybar) i + t • U i := by
                    intro i; funext m; refine Fin.cases ?_ (fun j => ?_) m
                    · simp [block, xc, hU0]
                    · simp [block]
                  refine ⟨h.1, fun i j => ?_, fun i => by rw [hblk]; exact h.2 i⟩
                  have := (hB i).2.2.1 _ (h.2 i) j
                  simpa [block] using this
                have hp := mem (ε/2) (by rw [abs_of_pos (by linarith)]; linarith)
                have hm := mem (-(ε/2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
                have hz : (xbar, ybar) ∈ openSegment ℝ
                    ((xbar + (ε/2) • v, fun i j => ybar i j + (ε/2) * U i j.succ) : Pt n p d)
                    (xbar + (-(ε/2)) • v, fun i j => ybar i j + (-(ε/2)) * U i j.succ) := by
                  refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, Prod.ext ?_ ?_⟩
                  · funext m; simp; ring
                  · funext i j; simp; ring
                have h1 := congrArg Prod.fst (hext.2 hp hm hz)
                simp only at h1
                have : (ε/2) • v = 0 := by
                  have := congrArg (fun x => x - xbar) h1
                  simpa using this
                rcases smul_eq_zero.1 this with h | h
                · linarith
                · exact h
              set F : Set (Fin n → ℝ) := {x | x ∈ P ∧ x - xbar ∈ D} with hFdef
              have hxF : xbar ∈ F := ⟨hxP, by simp⟩
              have hFface : IsFace P F := by
                refine ⟨?_, ⟨fun x hx => hx.1, ?_⟩⟩
                · intro x hx y hy a b ha hb hab
                  refine ⟨hPc hx.1 hy.1 ha hb hab, ?_⟩
                  have : a • x + b • y - xbar = a • (x - xbar) + b • (y - xbar) := by
                    obtain rfl : b = 1 - a := by linarith
                    module
                  rw [this]; exact D.add_mem (D.smul_mem a hx.2) (D.smul_mem b hy.2)
                · intro x1 hx1 x2 hx2 w hw hseg
                  refine ⟨hx1, ?_⟩
                  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 ((hDmem _).1 hw.2)
                  set r := ε / 2 with hr
                  have hr0 : 0 < r := by linarith
                  have hq : xbar + (-r) • (w - xbar) ∈ P :=
                    hεP (show dist (-r) 0 < ε by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hr0]; linarith)
                  obtain ⟨μ, ν, hμ, hν, hμν, rfl⟩ := hseg
                  have hκ : 0 < 1 + r * ν := by positivity
                  have hc := hPc hx2 hq (by positivity : 0 ≤ r * ν / (1 + r * ν))
                    (by positivity : 0 ≤ 1 / (1 + r * ν))
                    (by rw [← add_div, div_eq_one_iff_eq hκ.ne']; ring)
                  refine L1 P hPc xbar hxP x1 hx1 (r * μ / (1 + r * ν)) (by positivity) ?_
                  convert hc using 1
                  obtain rfl : ν = 1 - μ := by linarith
                  match_scalars <;> field_simp <;> ring
              have hWD : vectorSpan ℝ F ≤ D := by
                rw [vectorSpan_def]
                apply Submodule.span_le.2
                rintro _ ⟨x, hx, y, hy, rfl⟩
                simp only [vsub_eq_sub, SetLike.mem_coe]
                have : x - y = (x - xbar) - (y - xbar) := by abel
                rw [this]; exact D.sub_mem hx.2 hy.2
              set W := vectorSpan ℝ F with hW
              let sep : Finset (Fin p) → Prop := fun I => ∀ w ∈ W, (∀ i ∈ I, xc hpn w i = 0) → w = 0
              have hJsep : sep J := fun w hw h => hkey w (hWD hw) h
              obtain ⟨I, hImem, hImin⟩ := Finset.exists_min_image (J.powerset.filter sep) Finset.card
                ⟨J, Finset.mem_filter.2 ⟨Finset.mem_powerset_self J, hJsep⟩⟩
              obtain ⟨hIJ, hIsep⟩ := Finset.mem_filter.1 hImem
              rw [Finset.mem_powerset] at hIJ
              have hcard : I.card = Module.finrank ℝ W := by
                apply le_antisymm
                · by_contra hlt
                  push Not at hlt
                  let f : I → Module.Dual ℝ W := fun i =>
                    (LinearMap.proj (Fin.castLE hpn i.1) : (Fin n → ℝ) →ₗ[ℝ] ℝ) ∘ₗ W.subtype
                  have hnli : ¬ LinearIndependent ℝ f := by
                    intro hli
                    have := hli.fintype_card_le_finrank
                    rw [Subspace.dual_finrank_eq, Fintype.card_coe] at this
                    omega
                  obtain ⟨g, hg, i0, hi0⟩ := Fintype.not_linearIndependent_iff.1 hnli
                  have hsep' : sep (I.erase i0.1) := by
                    intro w hw hwz
                    apply hIsep w hw
                    intro i hi
                    by_cases h : i = i0.1
                    · subst h
                      have hsum : ∑ i : I, g i * w (Fin.castLE hpn i.1) = 0 := by
                        have := LinearMap.congr_fun hg ⟨w, hw⟩
                        simpa [f] using this
                      rw [Finset.sum_eq_single i0] at hsum
                      · rcases mul_eq_zero.1 hsum with h | h
                        · exact absurd h hi0
                        · exact h
                      · intro b _ hb
                        have hb' : b.1 ≠ i0.1 := fun e => hb (Subtype.ext e)
                        have := hwz b.1 (Finset.mem_erase.2 ⟨hb', b.2⟩)
                        simp only [xc] at this
                        rw [this, mul_zero]
                      · intro h; exact absurd (Finset.mem_univ _) h
                    · exact hwz i (Finset.mem_erase.2 ⟨h, hi⟩)
                  have h1 := hImin (I.erase i0.1) (Finset.mem_filter.2
                    ⟨Finset.mem_powerset.2 ((Finset.erase_subset _ _).trans hIJ), hsep'⟩)
                  have h2 := Finset.card_erase_lt_of_mem i0.2
                  omega
                · let ψ : W →ₗ[ℝ] (I → ℝ) := LinearMap.pi (fun i =>
                    (LinearMap.proj (Fin.castLE hpn i.1) : (Fin n → ℝ) →ₗ[ℝ] ℝ) ∘ₗ W.subtype)
                  have hinj : Function.Injective ψ := by
                    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
                    intro w hw
                    have := hIsep w.1 w.2 (fun i hi => by
                      have := congrFun hw ⟨i, hi⟩
                      simpa [ψ, xc] using this)
                    exact Subtype.ext this
                  have := LinearMap.finrank_le_finrank_of_injective hinj
                  simpa using this
              refine ⟨I, fun i => ⌊xc hpn xbar i⌋₊, F, fun i hi => (hint i (hIJ hi)).2, hFface,
                hcard.symm, ?_, fun i hi => (Finset.mem_filter.1 (hIJ hi)).2, fun i _ => hslice i⟩
              ext x
              simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
              constructor
              · rintro ⟨hx, hxG⟩
                have hmem : x - xbar ∈ W := by
                  have := vsub_mem_vectorSpan ℝ hx hxF
                  simpa using this
                have := hIsep _ hmem (fun i hi => by
                  have h1 := hxG i hi
                  have h2 := (hint i (hIJ hi)).1
                  simp only [xc, Pi.sub_apply] at h1 h2 ⊢
                  rw [h1, ← h2]; ring)
                exact sub_eq_zero.1 this
              · rintro rfl
                exact ⟨hxF, fun i hi => (hint i (hIJ hi)).1⟩
