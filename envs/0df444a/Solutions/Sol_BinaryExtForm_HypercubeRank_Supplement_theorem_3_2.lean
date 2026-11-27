-- Prove2me | solution 1 for BinaryExtForm.HypercubeRank.Supplement.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:52.625152+00:00
-- url     : https://prove2.me/submissions/eb1ecefc-c7f8-4061-9a0e-2d64fb5bdfa0

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
    (hN : ∀ i, IsNatural (B i)) (xbar : Fin n → ℝ) :
    xbar ∈ Prod.fst '' Set.extremePoints ℝ (BEF hpn P B) ↔
      ∃ (I : Finset (Fin p)) (α : Fin p → ℕ) (F : Set (Fin n → ℝ)),
        (∀ i ∈ I, α i ≤ k) ∧ IsFace P F ∧ affDim F = I.card ∧
        F ∩ G hpn I α = {xbar} := by
          classical
          set_option maxHeartbeats 0 in
          have hgeom : ∀ (E : Type) [AddCommGroup E] [Module ℝ E]
              (S : Set E) (hS : Convex ℝ S) (x : E), x ∈ S →
              ∃ (V : Submodule ℝ E) (F : Set E),
                IsFace S F ∧ x ∈ F ∧ vectorSpan ℝ F = V ∧
                (∀ u ∈ F, u - x ∈ V) ∧
                (∀ v, v ∈ V ↔ ∀ᶠ t : ℝ in nhds 0, x + t • v ∈ S) := by
            intro E _ _ S hS x hx
            let T : Set E := (fun u => u - x) '' S
            have hT : Convex ℝ T := by
              exact hS.affine_image (AffineMap.id ℝ E - AffineMap.const ℝ E x)
            let C : PointedCone ℝ E := (ConvexCone.hull ℝ T).toPointedCone
              (ConvexCone.subset_hull ⟨x, hx, sub_self x⟩)
            let V := C.lineal
            have hC : ∀ v, v ∈ C ↔ ∃ r : ℝ, 0 < r ∧ ∃ u ∈ S, v = r • (u - x) := by
              intro v
              change v ∈ ConvexCone.hull ℝ T ↔ _
              rw [ConvexCone.mem_hull_of_convex hT]
              constructor
              · rintro ⟨r, hr, w, ⟨u, hu, rfl⟩, hw⟩
                exact ⟨r, hr, u, hu, hw.symm⟩
              · rintro ⟨r, hr, u, hu, rfl⟩
                exact ⟨r, hr, u - x, ⟨u, hu, rfl⟩, rfl⟩
            have hsub : ∀ u ∈ S, u - x ∈ C := by
              intro u hu
              exact (hC _).2 ⟨1, zero_lt_one, u, hu, by simp⟩
            let F : Set E := {u ∈ S | u - x ∈ V}
            have hxF : x ∈ F := ⟨hx, by simp [V]⟩
            have hFconv : Convex ℝ F := by
              intro u hu w hw a b ha hb hab
              refine ⟨hS hu.1 hw.1 ha hb hab, ?_⟩
              have hid : a • u + b • w - x = a • (u-x) + b • (w-x) := by
                match_scalars <;> linarith
              rw [hid]
              exact V.add_mem (V.smul_mem a hu.2) (V.smul_mem b hw.2)
            have hFext : IsExtreme ℝ S F := by
              refine ⟨fun _ h => h.1, ?_⟩
              intro u hu w hw z hz hzseg
              refine ⟨hu, ?_⟩
              apply (PointedCone.IsFaceOf.lineal C).isExtreme.left_mem_of_mem_openSegment
                (hsub u hu) (hsub w hw) hz.2
              rcases hzseg with ⟨a,b,ha,hb,hab,hz⟩
              refine ⟨a,b,ha,hb,hab,?_⟩
              rw [← hz]
              match_scalars <;> linarith
            have hspan : vectorSpan ℝ F = V := by
              rw [vectorSpan_eq_span_vsub_set_right ℝ hxF]
              apply le_antisymm
              · apply Submodule.span_le.2
                rintro _ ⟨u, hu, rfl⟩
                exact hu.2
              · intro v hv
                obtain ⟨r, hr, u, hu, hvu⟩ := (hC v).1 hv.1
                have huV : u - x ∈ V := by
                  have hh := V.smul_mem r⁻¹ hv
                  simpa [hvu, smul_smul, hr.ne'] using hh
                rw [hvu]
                exact Submodule.smul_mem _ r (Submodule.subset_span ⟨u, ⟨hu, huV⟩, rfl⟩)
            have hevent : ∀ v, v ∈ V ↔ ∀ᶠ t : ℝ in nhds 0, x + t • v ∈ S := by
              intro v
              constructor
              · intro hv
                obtain ⟨r, hr, u, hu, hvu⟩ := (hC v).1 hv.1
                obtain ⟨s, hs, w, hw, hvw⟩ := (hC (-v)).1 hv.2
                have hnear : ∀ᶠ t : ℝ in nhds 0, t * r < 1 ∧ -t * s < 1 := by
                  have h₁ : ∀ᶠ t : ℝ in nhds 0, t * r < 1 :=
                    (by fun_prop : Continuous (fun t : ℝ => t * r)).continuousAt.eventually_lt_const (by simp)
                  have h₂ : ∀ᶠ t : ℝ in nhds 0, -t * s < 1 :=
                    (by fun_prop : Continuous (fun t : ℝ => -t * s)).continuousAt.eventually_lt_const (by simp)
                  exact h₁.and h₂
                filter_upwards [hnear] with t ht
                by_cases ht0 : 0 ≤ t
                · have hh := hS hx hu (sub_nonneg.mpr ht.1.le) (mul_nonneg ht0 hr.le)
                    (show (1-t*r) + t*r = 1 by ring)
                  convert hh using 1 <;> rw [hvu] <;> module
                · have hh := hS hx hw (sub_nonneg.mpr ht.2.le) (mul_nonneg (by linarith : 0 ≤ -t) hs.le)
                    (show (1- -t*s) + -t*s = 1 by ring)
                  have hid : t • v = (-t) • (-v) := by simp
                  rw [hid, hvw]
                  convert hh using 1 <;> module
              · intro hv
                obtain ⟨t, ht0, ht⟩ := hv.exists_gt
                have hpos : v ∈ C := by
                  apply (hC _).2
                  refine ⟨t⁻¹, inv_pos.mpr ht0, x+t•v, ht, ?_⟩
                  simp [smul_smul, ht0.ne']
                have hvneg : ∀ᶠ t : ℝ in nhds 0, x + t • (-v) ∈ S := by
                  have hn : Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
                    simpa using (continuous_neg.continuousAt : ContinuousAt (fun t : ℝ => -t) 0).tendsto
                  simpa using hn.eventually hv
                obtain ⟨s, hs0, hs⟩ := hvneg.exists_gt
                exact ⟨hpos, (hC _).2 ⟨s⁻¹, inv_pos.mpr hs0, x+s•(-v), hs,
                  by simp [smul_smul, hs0.ne']⟩⟩
            exact ⟨V, F, ⟨hFconv, hFext⟩, hxF, hspan, fun _ hu => hu.2, hevent⟩
          have hneg : Filter.Tendsto (fun t : ℝ => -t) (nhds 0) (nhds 0) := by
            simpa using (continuous_neg.continuousAt : ContinuousAt (fun t : ℝ => -t) 0).tendsto
          have hzero : ∀ (E : Type) [AddCommGroup E] [Module ℝ E]
              (S : Set E) (x : E), x ∈ Set.extremePoints ℝ S → ∀ v : E,
              (∀ᶠ t : ℝ in nhds 0, x + t • v ∈ S) → v = 0 := by
            intro E _ _ S x hx v hv
            have hn : ∀ᶠ t : ℝ in nhds 0, x + (-t) • v ∈ S := hneg.eventually hv
            obtain ⟨t, ht, hp, hm⟩ := (hv.and hn).exists_gt
            have heq : x + t • v = x := hx.2 hp hm
              ⟨(1/2:ℝ), (1/2:ℝ), by norm_num, by norm_num, by norm_num, by module⟩
            have hv0 : t • v = 0 := by simpa using (add_eq_left.mp heq : t • v = 0)
            exact (smul_eq_zero.mp hv0).resolve_left ht.ne'
          have hconv : Convex ℝ P := by
            obtain ⟨S, rfl⟩ := hP
            exact convex_convexHull _ _
          have hconvB : ∀ i, Convex ℝ (B i) := by
            intro i
            obtain ⟨S, hs⟩ := (hB i).1
            rw [hs]
            exact convex_convexHull _ _
          have hcompactB : ∀ i, IsCompact (B i) := by
            intro i
            obtain ⟨S, hs⟩ := (hB i).1
            rw [hs]
            exact S.finite_toSet.isCompact_convexHull ℝ
          have hbin_unique : ∀ i u, u ∈ B i → IsBinaryY u → ∀ v, v ∈ B i →
              yproj v = yproj u → v = u := by
            intro i u hu hub v hv hvy
            let S : Set (Fin (d+1) → ℝ) := {w ∈ B i | yproj w = yproj u}
            have hS : Convex ℝ S := by
              intro w hw z hz a b ha hb hab
              refine ⟨hconvB i hw.1 hz.1 ha hb hab, ?_⟩
              ext j
              change a * w j.succ + b * z j.succ = u j.succ
              have hwj := congrFun hw.2 j
              have hzj := congrFun hz.2 j
              change w j.succ = u j.succ at hwj
              change z j.succ = u j.succ at hzj
              rw [hwj, hzj, ← add_mul, hab, one_mul]
            have hf : ({t : ℝ | ∃ m : ℕ, m ≤ k ∧ t = m} : Set ℝ).Finite := by
              apply ((Set.finite_Iic k).image (fun m : ℕ => (m : ℝ))).subset
              rintro t ⟨m, hm, rfl⟩
              exact ⟨m, hm, rfl⟩
            have hmap : Set.MapsTo (fun w : Fin (d+1) → ℝ => w 0) S
                {t : ℝ | ∃ m : ℕ, m ≤ k ∧ t = m} := by
              intro w hw
              rw [← (hB i).2.2.2]
              refine ⟨w, ⟨hw.1, ?_⟩, rfl⟩
              intro j
              have hj := congrFun hw.2 j
              change w j.succ = u j.succ at hj
              rw [hj]
              exact hub j
            have h0 : v 0 = u 0 := hS.isPreconnected.constant_of_mapsTo hf.isDiscrete
              (continuous_apply 0).continuousOn hmap ⟨hv,hvy⟩ ⟨hu,rfl⟩
            ext j
            refine Fin.cases h0 (fun j => congrFun hvy j) j
          have hbinext : ∀ i u, u ∈ B i → IsBinaryY u → u ∈ Set.extremePoints ℝ (B i) := by
            intro i u hu hub
            refine ⟨hu, ?_⟩
            intro v hv w hw hseg
            apply hbin_unique i u hu hub v hv
            ext j
            rcases hseg with ⟨a,b,ha,hb,hab,heq⟩
            have hj := congrFun heq j.succ
            change a * v j.succ + b * w j.succ = u j.succ at hj
            have hvj := (hB i).2.2.1 v hv j
            have hwj := (hB i).2.2.1 w hw j
            change v j.succ = u j.succ
            rcases hub j with h0 | h1
            · rw [h0] at hj ⊢
              nlinarith [mul_nonneg hb.le hwj.1]
            · rw [h1] at hj ⊢
              nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hwj.2)]
          have hblockseg : ∀ (z u v : Pt n p d) i, z ∈ openSegment ℝ u v →
              block hpn z i ∈ openSegment ℝ (block hpn u i) (block hpn v i) := by
            intro z u v i hseg
            rcases hseg with ⟨a,b,ha,hb,hab,rfl⟩
            refine ⟨a,b,ha,hb,hab,?_⟩
            ext j
            refine Fin.cases ?_ (fun j => ?_) j <;> simp [block, xc]
          constructor
          · rintro ⟨⟨x, y⟩, hz, rfl⟩
            obtain ⟨V, F, hF, hxF, hspan, hdiff, hV⟩ := hgeom _ P hconv x hz.1.1
            have hiGeom := fun i => hgeom _ (B i) (hconvB i) (block hpn (x,y) i) (hz.1.2.2 i)
            choose W H hH hxH hWspan hWdiff hW using hiGeom
            have hkill : ∀ (v : Fin n → ℝ) (w : Fin p → Fin (d+1) → ℝ),
                v ∈ V → (∀ i, w i ∈ W i) → (∀ i, w i 0 = xc hpn v i) →
                v = 0 ∧ ∀ i, w i = 0 := by
              intro v w hv hw hweq
              let q : Pt n p d := (v, fun i j => w i j.succ)
              have hq : ∀ᶠ t : ℝ in nhds 0, (x,y) + t • q ∈ BEF hpn P B := by
                have hWall : ∀ᶠ t : ℝ in nhds 0, ∀ i, block hpn (x,y) i + t • w i ∈ B i :=
                  Filter.eventually_all.2 (fun i => (hW i (w i)).1 (hw i))
                filter_upwards [(hV v).1 hv, hWall] with t ht htW
                have hblock : ∀ i, block hpn ((x,y) + t • q) i = block hpn (x,y) i + t • w i := by
                  intro i
                  ext j
                  refine Fin.cases ?_ (fun j => ?_) j
                  · simp [block, xc, q, hweq]
                  · simp [block, q]
                refine ⟨ht, ?_, fun i => hblock i ▸ htW i⟩
                intro i j
                have hh := (hB i).2.2.1 _ (htW i) j
                simpa [block, q] using hh
              have hq0 := hzero _ _ (x,y) hz q hq
              have hv0 : v = 0 := congrArg Prod.fst hq0
              refine ⟨hv0, ?_⟩
              intro i
              ext j
              refine Fin.cases ?_ (fun j => ?_) j
              · rw [hweq, hv0]
                rfl
              · exact congrFun (congrFun (congrArg Prod.snd hq0) i) j
            have hWi0 : ∀ i w, w ∈ W i → w 0 = 0 → w = 0 := by
              intro i w hw hw0
              have hh := hkill 0 (Function.update 0 i w) V.zero_mem
                (by intro j; by_cases hji : j = i <;> simp [hji, hw, (W j).zero_mem])
                (by intro j; by_cases hji : j = i <;> simp [hji, hw0, xc])
              simpa using hh.2 i
            let J : Finset (Fin p) := Finset.univ.filter (fun i => block hpn (x,y) i ∈ Set.extremePoints ℝ (B i))
            have hsep : ∀ v ∈ V, (∀ i ∈ J, xc hpn v i = 0) → v = 0 := by
              intro v hv hvJ
              have hchoose : ∀ i, ∃ w ∈ W i, w 0 = xc hpn v i := by
                intro i
                by_cases hi : i ∈ J
                · exact ⟨0, (W i).zero_mem, (hvJ i hi).symm⟩
                · have hex : ∃ w ∈ W i, w 0 ≠ 0 := by
                    by_contra! hn
                    have hext : block hpn (x,y) i ∈ Set.extremePoints ℝ (B i) := by
                      refine ⟨hz.1.2.2 i, ?_⟩
                      intro u hu w hw hseg
                      have huH := (hH i).2.left_mem_of_mem_openSegment hu hw (hxH i) hseg
                      have hd := hWdiff i u huH
                      have he := hWi0 i _ hd (hn _ hd)
                      exact sub_eq_zero.mp he
                    exact hi (by simpa [J] using hext)
                  obtain ⟨w, hw, hw0⟩ := hex
                  refine ⟨(xc hpn v i / w 0) • w, (W i).smul_mem _ hw, ?_⟩
                  simp [hw0]
              choose w hw hweq using hchoose
              exact (hkill v w hv hw hweq).1
            let L : J → Module.Dual ℝ V := fun i =>
              (LinearMap.proj (Fin.castLE hpn i.val)).comp V.subtype
            have hLspan : Submodule.span ℝ (Set.range L) = ⊤ := by
              apply Submodule.span_eq_top_of_ne_zero
              intro v hv
              have hnv : ∃ i ∈ J, xc hpn (v : Fin n → ℝ) i ≠ 0 := by
                by_contra! hh
                exact hv (Subtype.ext (hsep v v.property hh))
              obtain ⟨i, hi, hvi⟩ := hnv
              exact ⟨L ⟨i,hi⟩, ⟨⟨i,hi⟩, rfl⟩, hvi⟩
            obtain ⟨κ, a, ha, hLa, hLI⟩ := exists_linearIndependent' ℝ L
            letI : Finite κ := Finite.of_injective a ha
            letI : Fintype κ := Fintype.ofFinite κ
            let I : Finset (Fin p) := Finset.univ.image (fun j : κ => (a j).val)
            have hI : ∀ i ∈ I, i ∈ J := by
              intro i hi
              obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
              exact (a j).property
            have hIcard : I.card = Module.finrank ℝ V := by
              have hb : Module.Basis κ ℝ (Module.Dual ℝ V) := Module.Basis.mk hLI (by rw [hLa, hLspan])
              change (Finset.univ.image (fun j : κ => (a j).val)).card = _
              rw [Finset.card_image_of_injective _ (show Function.Injective (fun j : κ => (a j).val) from Subtype.val_injective.comp ha)]
              simpa [Subspace.dual_finrank_eq] using (Module.finrank_eq_card_basis hb).symm
            have hsepI : ∀ v ∈ V, (∀ i ∈ I, xc hpn v i = 0) → v = 0 := by
              intro v hv hvi
              apply hsep v hv
              intro i hi
              have hLi : L ⟨i,hi⟩ ∈ Submodule.span ℝ (Set.range (L ∘ a)) := by
                rw [hLa, hLspan]
                trivial
              have hall : ∀ f ∈ Submodule.span ℝ (Set.range (L ∘ a)), f ⟨v,hv⟩ = 0 := by
                intro f hf
                induction hf using Submodule.span_induction with
                | mem f hf =>
                  obtain ⟨j, rfl⟩ := hf
                  exact hvi _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
                | zero => rfl
                | add f g hf hg hf0 hg0 => simp [hf0, hg0]
                | smul c f hf hf0 => simp [hf0]
              exact hall _ hLi
            have hInt : ∀ i ∈ I, ∃ m : ℕ, m ≤ k ∧ xc hpn x i = m := by
              intro i hi
              obtain ⟨m, hm⟩ := hN i (block hpn (x,y) i) (by simpa [J] using hI i hi)
              have hm' : xc hpn x i = (m : ℝ) := by simpa [block] using hm
              have hm0 : 0 ≤ m := by exact_mod_cast (hm' ▸ (hPk x hz.1.1 i).1)
              refine ⟨m.toNat, ?_, ?_⟩
              · have := (hPk x hz.1.1 i).2
                rw [hm'] at this
                have hmle : m ≤ (k : ℤ) := by exact_mod_cast this
                exact Int.toNat_le.mpr (by simpa using hmle)
              · rw [← Int.toNat_of_nonneg hm0] at hm'
                exact_mod_cast hm'
            let α : Fin p → ℕ := fun i => if hi : i ∈ I then (hInt i hi).choose else 0
            have hα : ∀ i ∈ I, α i ≤ k ∧ xc hpn x i = α i := by
              intro i hi
              simpa [α, hi] using (hInt i hi).choose_spec
            refine ⟨I, α, F, fun i hi => (hα i hi).1, hF, ?_, ?_⟩
            · change Module.finrank ℝ (vectorSpan ℝ F) = I.card
              rw [hspan]
              exact hIcard.symm
            · apply Set.eq_singleton_iff_unique_mem.2
              refine ⟨⟨hxF, fun i hi => (hα i hi).2⟩, ?_⟩
              intro u hu
              apply sub_eq_zero.mp
              apply hsepI _ (hdiff u hu.1)
              intro i hi
              change u (Fin.castLE hpn i) - x (Fin.castLE hpn i) = 0
              exact sub_eq_zero.mpr ((hu.2 i hi).trans (hα i hi).2.symm)
          · rintro ⟨I, α, F, hα, hF, hdim, hinter⟩
            have hxFG : xbar ∈ F ∩ G hpn I α := by rw [hinter]; exact Set.mem_singleton _
            have hxP : xbar ∈ P := hF.2.subset hxFG.1
            have hxα : ∀ i ∈ I, xc hpn xbar i = α i := hxFG.2
            have hslicene : ∀ i, (slice (B i) (xc hpn xbar i)).Nonempty := by
              intro i
              have hproj : Convex ℝ ((fun u : Fin (d+1) → ℝ => u 0) '' B i) :=
                (hconvB i).linear_image (LinearMap.proj 0)
              have h0 : (0:ℝ) ∈ (fun u : Fin (d+1) → ℝ => u 0) '' B i := by
                have hh : (0:ℝ) ∈ (fun u : Fin (d+1) → ℝ => u 0) '' {u | u ∈ B i ∧ IsBinaryY u} := by
                  rw [(hB i).2.2.2]
                  exact ⟨0, Nat.zero_le _, by simp⟩
                exact Set.image_mono (fun _ h => h.1) hh
              have hk : (k:ℝ) ∈ (fun u : Fin (d+1) → ℝ => u 0) '' B i := by
                have hh : (k:ℝ) ∈ (fun u : Fin (d+1) → ℝ => u 0) '' {u | u ∈ B i ∧ IsBinaryY u} := by
                  rw [(hB i).2.2.2]
                  exact ⟨k, le_rfl, rfl⟩
                exact Set.image_mono (fun _ h => h.1) hh
              have ht : xc hpn xbar i ∈ segment ℝ (0:ℝ) k := by
                rw [segment_eq_Icc (Nat.cast_nonneg k)]
                exact hPk xbar hxP i
              obtain ⟨u, hu, hu0⟩ := hproj.segment_subset h0 hk ht
              exact ⟨u, hu, hu0⟩
            have hchoose : ∀ i, ∃ u : Fin (d+1) → ℝ,
                u ∈ Set.extremePoints ℝ (slice (B i) (xc hpn xbar i)) ∧
                (i ∈ I → u ∈ Set.extremePoints ℝ (B i)) := by
              intro i
              by_cases hi : i ∈ I
              · have hm : (α i : ℝ) ∈ (fun u : Fin (d+1) → ℝ => u 0) '' {u | u ∈ B i ∧ IsBinaryY u} := by
                  rw [(hB i).2.2.2]
                  exact ⟨α i, hα i hi, rfl⟩
                obtain ⟨u, ⟨hu, hub⟩, hu0⟩ := hm
                have he := hbinext i u hu hub
                refine ⟨u, ⟨⟨hu, hu0.trans (hxα i hi).symm⟩, ?_⟩, fun _ => he⟩
                intro v hv w hw hseg
                exact he.2 hv.1 hw.1 hseg
              · have hc : IsCompact (slice (B i) (xc hpn xbar i)) :=
                  (hcompactB i).inter_right (isClosed_eq (continuous_apply 0) continuous_const)
                obtain ⟨u, hu⟩ := hc.extremePoints_nonempty (hslicene i)
                exact ⟨u, hu, fun h => (hi h).elim⟩
            choose u hu huI using hchoose
            let z : Pt n p d := (xbar, fun i => yproj (u i))
            have hzu : ∀ i, block hpn z i = u i := by
              intro i
              ext j
              refine Fin.cases ?_ (fun j => ?_) j
              · simpa [block, z] using (hu i).1.2.symm
              · rfl
            have hz : z ∈ BEF hpn P B := by
              refine ⟨hxP, ?_, fun i => hzu i ▸ (hu i).1.1⟩
              intro i j
              exact (hB i).2.2.1 (u i) (hu i).1.1 j
            refine ⟨z, ⟨hz, ?_⟩, rfl⟩
            intro v hv w hw hseg
            have hxseg : xbar ∈ openSegment ℝ v.1 w.1 := by
              rcases hseg with ⟨a,b,ha,hb,hab,heq⟩
              exact ⟨a,b,ha,hb,hab, congrArg Prod.fst heq⟩
            have hvF := hF.2.left_mem_of_mem_openSegment hv.1 hw.1 hxFG.1 hxseg
            have hwF := hF.2.right_mem_of_mem_openSegment hv.1 hw.1 hxFG.1 hxseg
            have hIeq : ∀ i ∈ I, block hpn v i = u i ∧ block hpn w i = u i := by
              intro i hi
              have hs := hblockseg z v w i hseg
              rw [hzu] at hs
              exact (mem_extremePoints.mp (huI i hi)).2 _ (hv.2.2 i) _ (hw.2.2 i) hs
            have hvx : v.1 = xbar := by
              apply Set.mem_singleton_iff.mp
              rw [← hinter]
              refine ⟨hvF, ?_⟩
              intro i hi
              have hh := congrFun (hIeq i hi).1 0
              change xc hpn v.1 i = u i 0 at hh
              exact hh.trans ((hu i).1.2.trans (hxα i hi))
            have hwx : w.1 = xbar := by
              apply Set.mem_singleton_iff.mp
              rw [← hinter]
              refine ⟨hwF, ?_⟩
              intro i hi
              have hh := congrFun (hIeq i hi).2 0
              change xc hpn w.1 i = u i 0 at hh
              exact hh.trans ((hu i).1.2.trans (hxα i hi))
            have hveq : ∀ i, block hpn v i = u i := by
              intro i
              have hs := hblockseg z v w i hseg
              rw [hzu] at hs
              exact (hu i).2 ⟨hv.2.2 i, by simp [block, hvx]⟩
                ⟨hw.2.2 i, by simp [block, hwx]⟩ hs
            apply Prod.ext hvx
            funext i j
            exact congrFun (hveq i) j.succ
