-- Prove2me | solution 1 for BasicPackArb.Main.Supplement.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:21:43.376261+00:00
-- url     : https://prove2.me/submissions/fe0b9764-8d11-4a4d-ba02-afd77e886cbc

import Definitions.Def_BasicPackArb_Main_Supplement_Polyhedron

set_option autoImplicit false

open BasicPackArb
open BasicPackArb.Main
open BasicPackArb.Main.Supplement

/-- Theorem 3.2, p. 6: existence, integrality and the exact extreme-point set. -/
theorem solution {V Arc S : Type} [Fintype V] [Fintype S]
    [DecidableEq V] (D : Digraph V Arc) (π : S → V)
    (M : Matroid S) (hground : M.E = Set.univ) :
    ((∃ T : S → Arborescence D, IsBasicPacking D π M T) ↔
      (packingPolyhedron D π M).Nonempty) ∧
    ((packingPolyhedron D π M).Nonempty →
      IntegralPolyhedron (packingPolyhedron D π M) ∧
      (packingPolyhedron D π M).extremePoints ℝ =
        {x | ∃ T : S → Arborescence D, IsBasicPacking D π M T ∧ x = packingVector D T}) := by
          classical
          -- rank of a base, as a finset
          have hbase : ∀ B : Finset S, M.IsBase (B : Set S) → B.card = rank M Set.univ := by
            intro B hB
            have h1 : M.eRk Set.univ = (B.card : ℕ∞) := by
              rw [← Set.encard_coe_eq_coe_finsetCard, hB.encard_eq_eRank, ← Matroid.eRk_ground,
                hground]
            unfold rank
            rw [h1]; simp
          have hindep : ∀ (I : Finset S) (Q : Set S), M.Indep (I : Set S) → (I : Set S) ⊆ Q →
              I.card ≤ rank M Q := by
            intro I Q hI hIQ
            have h1 : (I.card : ℕ∞) ≤ M.eRk Q := by
              rw [← Set.encard_coe_eq_coe_finsetCard, ← hI.eRk_eq_encard]; exact M.eRk_mono hIQ
            have hfin : M.eRk Q ≠ ⊤ :=
              (Matroid.IsRkFinite.eRk_lt_top (M.isRkFinite_of_finite (Set.toFinite Q))).ne
            have := ENat.toNat_le_toNat h1 hfin
            simpa [rank] using this
          -- arc count of an arborescence
          have harb : ∀ A : Arborescence D, A.arcs.card + 1 = A.verts.card := by
            intro A
            have h1 : A.arcs.card = (A.verts.erase A.root).card := by
              apply Finset.card_nbij D.head
              · intro a ha
                simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff]
                exact ⟨A.head_mem a ha, A.root_inDeg a ha⟩
              · intro a ha b hb hab
                have hne : D.head a ≠ A.root := A.root_inDeg a ha
                obtain ⟨c, _, hc⟩ := A.inDeg_one (D.head a) (A.head_mem a ha) hne
                exact (hc a ⟨ha, rfl⟩).trans (hc b ⟨hb, hab.symm⟩).symm
              · intro v hv
                simp only [Finset.coe_erase, Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff] at hv
                obtain ⟨a, ⟨ha, hav⟩, _⟩ := A.inDeg_one v hv.1 hv.2
                exact ⟨a, ha, hav⟩
            rw [h1, Finset.card_erase_add_one A.root_mem]
          -- crossing lemma
          have hcross : ∀ (A : Arborescence D) (X : Finset V) (u w : V),
              Relation.ReflTransGen (fun x y => ∃ a ∈ A.arcs, D.tail a = x ∧ D.head a = y) u w →
              u ∉ X → w ∈ X → ∃ a ∈ A.arcs, D.tail a ∉ X ∧ D.head a ∈ X := by
            intro A X u w h hu hw
            induction h with
            | refl => exact absurd hw hu
            | tail hub hbc ih =>
              rename_i b c
              obtain ⟨a, ha, hta, hha⟩ := hbc
              by_cases hb : b ∈ X
              · exact ih hb
              · exact ⟨a, ha, hta ▸ hb, hha ▸ hw⟩
          have easy : ∀ T : S → Arborescence D, IsBasicPacking D π M T →
              packingVector D T ∈ packingPolyhedron D π M := by
            intro T hT
            obtain ⟨hroot, hdisj, hB⟩ := hT
            set U : Finset Arc := Finset.univ.biUnion (fun s => (T s).arcs) with hU
            have hUsub : U ⊆ D.arcs := by
              intro a ha
              simp only [hU, Finset.mem_biUnion, Finset.mem_univ, true_and] at ha
              obtain ⟨s, hs⟩ := ha
              exact (T s).arcs_subset hs
            have hsum : ∀ F : Finset Arc, arcSum D (packingVector D T) F = ((U ∩ F).card : ℝ) := by
              intro F
              unfold arcSum packingVector
              calc _ = ∑ a ∈ D.arcs, (if a ∈ U ∩ F then (1:ℝ) else 0) := by
                    rw [← Finset.sum_coe_sort D.arcs]
                    apply Finset.sum_congr rfl
                    intro a _
                    by_cases h1 : a.val ∈ F <;> by_cases h2 : ∃ s, a.val ∈ (T s).arcs <;>
                      simp [h1, h2, hU, Finset.mem_inter]
                    all_goals (first | tauto | (obtain ⟨s, hs⟩ := h2; exact absurd hs (by simp_all)))
                _ = ((U ∩ F).card : ℝ) := by
                    rw [Finset.sum_boole]
                    congr 2
                    ext a
                    simp only [Finset.mem_filter, Finset.mem_inter]
                    constructor
                    · intro h; exact h.2
                    · intro h; exact ⟨hUsub h.1, h⟩
            have hBv : ∀ v : V, (Finset.univ.filter (fun s => v ∈ (T s).verts)).card = rank M Set.univ := by
              intro v
              apply hbase
              convert hB v using 1
              ext s; simp
            refine ⟨?_, ?_, ?_⟩
            · intro a
              unfold packingVector
              split_ifs <;> norm_num
            · intro X hX
              obtain ⟨v, hv⟩ := hX
              rw [hsum]
              set Bv := Finset.univ.filter (fun s => v ∈ (T s).verts)
              set P1 := Bv.filter (fun s => π s ∈ X)
              set P2 := Bv.filter (fun s => π s ∉ X)
              have hP : P1.card + P2.card = Bv.card := Finset.card_filter_add_card_filter_not _
              have hP1 : P1.card ≤ rank M (π ⁻¹' (X : Set V)) := by
                apply hindep
                · apply (hB v).indep.subset
                  intro s hs
                  simp [P1, Bv] at hs
                  exact hs.1
                · intro s hs
                  simp [P1, Bv] at hs
                  exact hs.2
              have hP2 : P2.card ≤ (U ∩ D.enteringArcs X).card := by
                calc P2.card = ∑ s ∈ P2, 1 := by simp
                  _ ≤ ∑ s ∈ P2, ((T s).arcs ∩ D.enteringArcs X).card := by
                    apply Finset.sum_le_sum
                    intro s hs
                    simp only [P2, Bv, Finset.mem_filter, Finset.mem_univ, true_and] at hs
                    obtain ⟨a, ha, hta, hha⟩ :=
                      hcross (T s) X _ _ ((T s).reach v hs.1) (by rw [hroot]; exact hs.2) hv
                    apply Finset.card_pos.mpr
                    refine ⟨a, Finset.mem_inter.mpr ⟨ha, ?_⟩⟩
                    simp [Digraph.enteringArcs, (T s).arcs_subset ha, hta, hha]
                  _ = (P2.biUnion (fun s => (T s).arcs ∩ D.enteringArcs X)).card := by
                    rw [Finset.card_biUnion]
                    intro s _ t _ hst
                    exact Finset.disjoint_of_subset_left Finset.inter_subset_left
                      (Finset.disjoint_of_subset_right Finset.inter_subset_left (hdisj s t hst))
                  _ ≤ (U ∩ D.enteringArcs X).card := by
                    apply Finset.card_le_card
                    intro a ha
                    simp only [Finset.mem_biUnion, Finset.mem_inter] at ha
                    obtain ⟨s, _, ha1, ha2⟩ := ha
                    simp only [Finset.mem_inter, hU, Finset.mem_biUnion, Finset.mem_univ, true_and]
                    exact ⟨⟨s, ha1⟩, ha2⟩
              have hBv' : Bv.card = rank M Set.univ := hBv v
              have h3 : rank M Set.univ ≤ (U ∩ D.enteringArcs X).card + rank M (π ⁻¹' (X : Set V)) := by
                omega
              exact_mod_cast h3
            · rw [hsum, Finset.inter_eq_left.mpr hUsub]
              have hUc : U.card = ∑ s, (T s).arcs.card := by
                rw [hU, Finset.card_biUnion]
                intro s _ t _ hst
                exact hdisj s t hst
              have hV : ∑ s, (T s).verts.card = rank M Set.univ * Fintype.card V := by
                calc ∑ s, (T s).verts.card
                    = ∑ s, ∑ v, (if v ∈ (T s).verts then 1 else 0) := by
                      apply Finset.sum_congr rfl
                      intro s _
                      rw [Finset.sum_boole]; simp
                  _ = ∑ v, ∑ s, (if v ∈ (T s).verts then 1 else 0) := Finset.sum_comm
                  _ = ∑ v : V, rank M Set.univ := by
                      apply Finset.sum_congr rfl
                      intro v _
                      rw [Finset.sum_boole, hBv v]; simp
                  _ = rank M Set.univ * Fintype.card V := by
                      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
              have hS : ∑ s, (T s).verts.card = U.card + Fintype.card S := by
                rw [hUc, Finset.card_univ.symm, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
                exact Finset.sum_congr rfl (fun s _ => (harb (T s)).symm)
              have h4 : (U.card : ℝ) + Fintype.card S = (rank M Set.univ : ℝ) * Fintype.card V := by
                exact_mod_cast hS.symm.trans hV
              linarith
          set P := packingPolyhedron D π M with hPdef
          set Z := {x | x ∈ P ∧ ∀ i, ∃ z : ℤ, x i = z} with hZ
          -- linearity of arcSum
          have hlin : ∀ (x y : ArcVector D) (a b : ℝ) (F : Finset Arc),
              arcSum D (a • x + b • y) F = a * arcSum D x F + b * arcSum D y F := by
            intro x y a b F
            unfold arcSum
            rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> simp
          have hconv : Convex ℝ P := by
            intro x hx y hy a b ha hb hab
            obtain ⟨hx1, hx2, hx3⟩ := hx
            obtain ⟨hy1, hy2, hy3⟩ := hy
            refine ⟨?_, ?_, ?_⟩
            · intro i
              have := hx1 i; have := hy1 i
              simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
              constructor <;> nlinarith
            · intro X hX
              rw [hlin]
              have := hx2 X hX; have := hy2 X hX
              have e : (rank M Set.univ : ℝ) = a * rank M Set.univ + b * rank M Set.univ := by
                rw [← add_mul, hab, one_mul]
              have e2 : (rank M (π ⁻¹' (X : Set V)) : ℝ) =
                  a * rank M (π ⁻¹' (X : Set V)) + b * rank M (π ⁻¹' (X : Set V)) := by
                rw [← add_mul, hab, one_mul]
              nlinarith
            · rw [hlin, hx3, hy3, ← add_mul, hab, one_mul]
          -- DEEP FACT 1a: Theorem 1.6 (sufficiency) of the paper, in the `Main` vocabulary
          have thm16 : ∀ D' : Digraph V Arc, MIndependent π M → MConnected D' π M →
              ∃ T : S → Arborescence D', IsBasicPacking D' π M T := by
            intro D' hind hconn
            let Inv : (S → Arborescence D') → Prop := fun T =>
              (∀ s, (T s).root = π s) ∧ (∀ s s', s ≠ s' → Disjoint (T s).arcs (T s').arcs) ∧
              (∀ v, M.Indep {s | v ∈ (T s).verts}) ∧
              (∀ X : Finset V, X.Nonempty → M.eRk Set.univ ≤
                 (((D'.enteringArcs X).filter (fun a => ∀ s, a ∉ (T s).arcs)).card : ℕ∞) +
                   M.eRk {s | ∃ v ∈ X, v ∈ (T s).verts})
            let μ : (S → Arborescence D') → ℕ := fun T => ∑ s, (T s).verts.card
            have extA : ∀ (A : Arborescence D') (a : Arc), a ∈ D'.arcs → D'.tail a ∈ A.verts →
                D'.head a ∉ A.verts → ∃ A' : Arborescence D', A'.verts = insert (D'.head a) A.verts ∧
                  A'.arcs = insert a A.arcs ∧ A'.root = A.root := by
              intro A a ha hta hha
              refine ⟨Arborescence.mk (insert (D'.head a) A.verts) (insert a A.arcs) A.root
                (Finset.insert_subset ha A.arcs_subset) ?_ ?_ (Finset.mem_insert_of_mem A.root_mem)
                ?_ ?_ ?_, rfl, rfl, rfl⟩
              · intro b hb
                rcases Finset.mem_insert.mp hb with rfl | hb
                · exact Finset.mem_insert_of_mem hta
                · exact Finset.mem_insert_of_mem (A.tail_mem b hb)
              · intro b hb
                rcases Finset.mem_insert.mp hb with rfl | hb
                · exact Finset.mem_insert_self _ _
                · exact Finset.mem_insert_of_mem (A.head_mem b hb)
              · intro b hb
                rcases Finset.mem_insert.mp hb with rfl | hb
                · intro h; exact hha (h ▸ A.root_mem)
                · exact A.root_inDeg b hb
              · intro v hv hvr
                rcases Finset.mem_insert.mp hv with rfl | hv
                · refine ⟨a, ⟨Finset.mem_insert_self _ _, rfl⟩, ?_⟩
                  rintro b ⟨hb, hbv⟩
                  rcases Finset.mem_insert.mp hb with rfl | hb
                  · rfl
                  · exact absurd (hbv ▸ A.head_mem b hb) hha
                · obtain ⟨b, ⟨hb, hbv⟩, hu⟩ := A.inDeg_one v hv hvr
                  refine ⟨b, ⟨Finset.mem_insert_of_mem hb, hbv⟩, ?_⟩
                  rintro c ⟨hc, hcv⟩
                  rcases Finset.mem_insert.mp hc with hca | hc
                  · exfalso; apply hha; rw [← hca, hcv]; exact hv
                  · exact hu c ⟨hc, hcv⟩
              · have mono : ∀ v, Relation.ReflTransGen (fun x y => ∃ b ∈ A.arcs, D'.tail b = x ∧ D'.head b = y) A.root v →
                    Relation.ReflTransGen (fun x y => ∃ b ∈ insert a A.arcs, D'.tail b = x ∧ D'.head b = y) A.root v := by
                  intro v h
                  refine Relation.ReflTransGen.mono ?_ _ _ h
                  intro x y hxy
                  obtain ⟨b, hb, h1, h2⟩ := hxy
                  exact ⟨b, Finset.mem_insert_of_mem hb, h1, h2⟩
                intro v hv
                rcases Finset.mem_insert.mp hv with rfl | hv
                · exact (mono _ (A.reach _ hta)).tail ⟨a, Finset.mem_insert_self _ _, rfl, rfl⟩
                · exact mono _ (A.reach v hv)
            have ext : ∀ T, Inv T → ∀ (a : Arc) (s : S), a ∈ D'.arcs → (∀ s', a ∉ (T s').arcs) →
                D'.tail a ∈ (T s).verts → D'.head a ∉ (T s).verts →
                M.Indep (insert s {s' | D'.head a ∈ (T s').verts}) →
                (∀ X : Finset V, X.Nonempty → D'.head a ∈ X → D'.tail a ∉ X →
                  M.eRk Set.univ + 1 ≤
                   (((D'.enteringArcs X).filter (fun a => ∀ s, a ∉ (T s).arcs)).card : ℕ∞) +
                    M.eRk (insert s {s' | ∃ v ∈ X, v ∈ (T s').verts})) →
                ∃ T', Inv T' ∧ μ T < μ T' := by
              intro T hT a s ha hfree hta hha hind hX
              obtain ⟨A', hv, harcs, hroot⟩ := extA (T s) a ha hta hha
              set T' := Function.update T s A' with hT'
              have vs : ∀ s', (T' s').verts = if s' = s then insert (D'.head a) (T s).verts else (T s').verts := by
                intro s'; by_cases h : s' = s
                · subst h; simp [hT', hv]
                · simp [hT', h]
              have as : ∀ s', (T' s').arcs = if s' = s then insert a (T s).arcs else (T s').arcs := by
                intro s'; by_cases h : s' = s
                · subst h; simp [hT', harcs]
                · simp [hT', h]
              refine ⟨T', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
              · intro s'; by_cases h : s' = s
                · subst h; simp [hT', hroot, hT.1]
                · simp [hT', h, hT.1]
              · intro s1 s2 h12
                rw [as, as]
                have hd := hT.2.1
                split_ifs with h1 h2 h2
                · exact absurd (h1.trans h2.symm) h12
                · subst h1
                  rw [Finset.disjoint_insert_left]
                  exact ⟨hfree s2, hd _ _ h12⟩
                · subst h2
                  rw [Finset.disjoint_insert_right]
                  exact ⟨hfree s1, hd _ _ h12⟩
                · exact hd _ _ h12
              · intro v
                by_cases hvw : v = D'.head a
                · subst hvw
                  convert hind using 1
                  ext s'; simp only [vs, Set.mem_ofPred_eq, Set.mem_insert_iff]
                  by_cases h : s' = s <;> simp [h]
                · convert hT.2.2.1 v using 1
                  ext s'; simp only [vs, Set.mem_ofPred_eq]
                  by_cases h : s' = s <;> simp [h, hvw]
              · intro X hXne
                have hF : ((D'.enteringArcs X).filter (fun b => ∀ s, b ∉ (T' s).arcs)) =
                    ((D'.enteringArcs X).filter (fun b => ∀ s, b ∉ (T s).arcs)).erase a := by
                  ext b
                  simp only [Finset.mem_filter, Finset.mem_erase, as]
                  constructor
                  · rintro ⟨h1, h2⟩
                    have hba : b ≠ a := by
                      intro hb; have := h2 s; simp [hb] at this
                    refine ⟨hba, h1, fun s' hs' => ?_⟩
                    have := h2 s'
                    split_ifs at this with h
                    · subst h; exact this (Finset.mem_insert_of_mem hs')
                    · exact this hs'
                  · rintro ⟨hba, h1, h2⟩
                    refine ⟨h1, fun s' => ?_⟩
                    split_ifs with h
                    · subst h; intro hb
                      rcases Finset.mem_insert.mp hb with hb | hb
                      · exact hba hb
                      · exact h2 s' hb
                    · exact h2 s'
                have hsub : {s' | ∃ v ∈ X, v ∈ (T s').verts} ⊆ {s' | ∃ v ∈ X, v ∈ (T' s').verts} := by
                  rintro s' ⟨v, hvX, hv'⟩
                  refine ⟨v, hvX, ?_⟩
                  rw [vs]; split_ifs with h
                  · subst h; exact Finset.mem_insert_of_mem hv'
                  · exact hv'
                by_cases haX : a ∈ ((D'.enteringArcs X).filter (fun b => ∀ s, b ∉ (T s).arcs))
                · have hent := (Finset.mem_filter.mp haX).1
                  simp only [Digraph.enteringArcs, Finset.mem_filter] at hent
                  have h := hX X hXne hent.2.2 hent.2.1
                  have hsub2 : insert s {s' | ∃ v ∈ X, v ∈ (T s').verts} ⊆
                      {s' | ∃ v ∈ X, v ∈ (T' s').verts} := by
                    intro s' hs'
                    rcases hs' with rfl | hs'
                    · refine ⟨D'.head a, hent.2.2, ?_⟩
                      rw [vs, if_pos rfl]; exact Finset.mem_insert_self _ _
                    · exact hsub hs'
                  rw [hF]
                  have hc := Finset.card_erase_add_one haX
                  have hm := M.eRk_mono hsub2
                  set c := ((D'.enteringArcs X).filter (fun b => ∀ s, b ∉ (T s).arcs)).erase a
                  set F := ((D'.enteringArcs X).filter (fun b => ∀ s, b ∉ (T s).arcs))
                  rw [← hc] at h
                  push_cast at h
                  have h2 : M.eRk Set.univ + 1 ≤ (c.card : ℕ∞) + M.eRk {s' | ∃ v ∈ X, v ∈ (T' s').verts} + 1 := by
                    calc M.eRk Set.univ + 1 ≤ (c.card : ℕ∞) + 1 + M.eRk (insert s {s' | ∃ v ∈ X, v ∈ (T s').verts}) := h
                      _ ≤ (c.card : ℕ∞) + 1 + M.eRk {s' | ∃ v ∈ X, v ∈ (T' s').verts} := by gcongr
                      _ = _ := by ring
                  exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h2
                · rw [hF, Finset.erase_eq_of_notMem haX]
                  exact (hT.2.2.2 X hXne).trans (by gcongr; exact M.eRk_mono hsub)
              · show ∑ s, (T s).verts.card < ∑ s, (T' s).verts.card
                apply Finset.sum_lt_sum
                · intro s' _; rw [vs]; split_ifs with h
                  · subst h; exact Finset.card_le_card (Finset.subset_insert _ _)
                  · exact le_rfl
                · refine ⟨s, Finset.mem_univ _, ?_⟩
                  rw [vs, if_pos rfl, Finset.card_insert_of_notMem hha]; omega
            have exist : ∀ T, Inv T → (∃ v, ¬ M.IsBase {s | v ∈ (T s).verts}) →
                ∃ (a : Arc) (s : S), a ∈ D'.arcs ∧ (∀ s', a ∉ (T s').arcs) ∧
                D'.tail a ∈ (T s).verts ∧ D'.head a ∉ (T s).verts ∧
                M.Indep (insert s {s' | D'.head a ∈ (T s').verts}) ∧
                (∀ X : Finset V, X.Nonempty → D'.head a ∈ X → D'.tail a ∉ X →
                  M.eRk Set.univ + 1 ≤
                   (((D'.enteringArcs X).filter (fun a => ∀ s, a ∉ (T s).arcs)).card : ℕ∞) +
                    M.eRk (insert s {s' | ∃ v ∈ X, v ∈ (T s').verts})) := by
              intro T hT hnb
              have hT3 := hT.2.2.1
              have hT4 := hT.2.2.2
              have hrk : ∀ Q : Set S, M.eRk Q = (rank M Q : ℕ∞) := by
                intro Q
                unfold rank
                rw [ENat.natCast_toNat]
                exact (Matroid.IsRkFinite.eRk_lt_top (M.isRkFinite_of_finite (Set.toFinite Q))).ne
              have hsub : ∀ P Q : Set S, rank M (P ∩ Q) + rank M (P ∪ Q) ≤ rank M P + rank M Q := by
                intro P Q
                have h := M.eRk_inter_add_eRk_union_le P Q
                rw [hrk, hrk, hrk, hrk] at h
                exact_mod_cast h
              have hmono : ∀ P Q : Set S, P ⊆ Q → rank M P ≤ rank M Q := by
                intro P Q h
                have := M.eRk_mono h
                rw [hrk, hrk] at this
                exact_mod_cast this
              have claim21 : ∀ (P Q : Set S) (s : S),
                  rank M (P ∩ Q) + rank M (P ∪ Q) = rank M P + rank M Q →
                  rank M (insert s P) = rank M P → rank M (insert s Q) = rank M Q →
                  rank M (insert s (P ∩ Q)) = rank M (P ∩ Q) := by
                intro P Q s heq hP hQ
                have h1 := hsub (insert s P) (insert s Q)
                rw [← Set.insert_inter_distrib, ← Set.insert_union_distrib] at h1
                have h2 := hmono (P ∪ Q) (insert s (P ∪ Q)) (Set.subset_insert _ _)
                have h3 := hmono (P ∩ Q) (insert s (P ∩ Q)) (Set.subset_insert _ _)
                omega
              have hcl : ∀ (Q : Set S) (s : S), s ∈ M.closure Q ↔ rank M (insert s Q) = rank M Q := by
                intro Q s
                constructor
                · intro h
                  have e := M.eRk_insert_closure_eq s Q
                  rw [Set.insert_eq_of_mem h, Matroid.eRk_closure_eq, hrk, hrk] at e
                  exact_mod_cast e.symm
                · intro h
                  by_contra h'
                  have e := Matroid.eRk_insert_eq_add_one (M := M) (e := s) (X := Q)
                    ⟨by rw [hground]; trivial, h'⟩
                  rw [hrk, hrk, h] at e
                  have : ((rank M Q : ℕ) : ℕ∞) + 1 = ((rank M Q + 1 : ℕ) : ℕ∞) := by push_cast; rfl
                  rw [this] at e
                  have := ENat.coe_inj.mp e
                  omega
              have hcleq : ∀ P Q : Set S, P ⊆ Q → rank M Q ≤ rank M P → M.closure P = M.closure Q := by
                intro P Q h1 h2
                apply Matroid.IsRkFinite.closure_eq_closure_of_subset_of_eRk_ge_eRk
                  (M.isRkFinite_of_finite (Set.toFinite P)) h1
                rw [hrk, hrk]; exact_mod_cast h2
              have dsub : ∀ (p : Arc → Prop) [DecidablePred p] (X Y : Finset V),
                  ((D'.enteringArcs (X ∩ Y)).filter p).card + ((D'.enteringArcs (X ∪ Y)).filter p).card ≤
                    ((D'.enteringArcs X).filter p).card + ((D'.enteringArcs Y).filter p).card := by
                intro p _ X Y
                simp only [Digraph.enteringArcs, Finset.filter_filter, Finset.card_filter]
                rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                apply Finset.sum_le_sum
                intro a _
                by_cases h1 : D'.tail a ∈ X <;> by_cases h2 : D'.tail a ∈ Y <;>
                  by_cases h3 : D'.head a ∈ X <;> by_cases h4 : D'.head a ∈ Y <;> by_cases h5 : p a <;>
                  simp [h1, h2, h3, h4, h5]
              set fr : Finset V → ℕ := fun X =>
                ((D'.enteringArcs X).filter (fun a => ∀ s, a ∉ (T s).arcs)).card with hfr
              set SX : Finset V → Set S := fun X => {s | ∃ v ∈ X, v ∈ (T s).verts} with hSX
              set Sv : V → Set S := fun v => {s | v ∈ (T s).verts} with hSv
              set k := rank M Set.univ with hk
              have hInv : ∀ X : Finset V, X.Nonempty → k ≤ fr X + rank M (SX X) := by
                intro X hX
                have h := hT4 X hX
                rw [hrk, hrk] at h
                exact_mod_cast h
              have hSvX : ∀ v X, v ∈ X → Sv v ⊆ SX X := fun v X hv s hs => ⟨v, hv, hs⟩
              let W : V → V → S → Finset V → Prop := fun u v s X =>
                X.Nonempty ∧ fr X + rank M (SX X) = k ∧ v ∈ X ∧ u ∉ X ∧ s ∈ M.closure (SX X)
              let Bad : Arc → S → Prop := fun a s =>
                a ∈ D'.arcs ∧ (∀ s', a ∉ (T s').arcs) ∧ s ∈ Sv (D'.tail a) ∧
                  s ∉ M.closure (Sv (D'.head a))
              by_contra hno
              have stepA : ∀ a s, Bad a s → ∃ X, W (D'.tail a) (D'.head a) s X := by
                rintro a s ⟨ha, hfree, hs, hns⟩
                have hns' : s ∉ Sv (D'.head a) := fun h =>
                  hns (M.subset_closure _ (by rw [hground]; exact Set.subset_univ _) h)
                have hind : M.Indep (insert s (Sv (D'.head a))) :=
                  (hT3 _).insert_indep_iff.mpr (Or.inl ⟨by rw [hground]; trivial, hns⟩)
                push_neg at hno
                obtain ⟨X, hXne, hvX, huX, hlt⟩ := hno a s ha hfree hs hns' hind
                rw [hrk, hrk] at hlt
                have hlt' : fr X + rank M (insert s (SX X)) < k + 1 := by exact_mod_cast hlt
                have h1 := hInv X hXne
                have h2 := hmono (SX X) _ (Set.subset_insert s (SX X))
                refine ⟨X, hXne, by omega, hvX, huX, (hcl _ _).mpr (by omega)⟩
              let R : Finset V → V → V → Prop := fun X x y =>
                ∃ b ∈ D'.arcs, (∀ s, b ∉ (T s).arcs) ∧ D'.tail b = x ∧ D'.head b = y ∧ x ∈ X ∧ y ∈ X
              have hEsub : ∀ Q : Set S, Q ⊆ M.E := fun Q => by rw [hground]; exact Set.subset_univ _
              have path : ∀ (X : Finset V) (v : V), (∀ b ∈ D'.arcs, (∀ s, b ∉ (T s).arcs) →
                  D'.tail b ∈ X → D'.head b ∈ X → Sv (D'.tail b) ⊆ M.closure (Sv (D'.head b))) →
                  ∀ y, Relation.ReflTransGen (R X) y v → Sv y ⊆ M.closure (Sv v) := by
                intro X v hg y h
                induction h using Relation.ReflTransGen.head_induction_on with
                | refl => exact M.subset_closure _ (hEsub _)
                | head hab _ ih =>
                  obtain ⟨b, hb, hf, h1, h2, h3, h4⟩ := hab
                  subst h1; subst h2
                  exact (hg b hb hf h3 h4).trans (M.closure_subset_closure_of_subset_closure ih)
              by_cases hex : ∃ a s, Bad a s
              swap
              · have hex' : ∀ a s, ¬ Bad a s := fun a s h => hex ⟨a, s, h⟩
                obtain ⟨v, hv⟩ := hnb
                apply hv
                have hg : ∀ b ∈ D'.arcs, (∀ s, b ∉ (T s).arcs) → D'.tail b ∈ (Finset.univ : Finset V) →
                    D'.head b ∈ (Finset.univ : Finset V) → Sv (D'.tail b) ⊆ M.closure (Sv (D'.head b)) := by
                  intro b hb hf _ _ s hs
                  by_contra hc
                  exact hex' b s ⟨hb, hf, hs, hc⟩
                set Z := Finset.univ.filter (fun y => Relation.ReflTransGen (R Finset.univ) y v) with hZ
                have hvZ : v ∈ Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
                have hfr0 : fr Z = 0 := by
                  simp only [hfr]
                  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
                  intro b hb hf
                  simp only [Digraph.enteringArcs, Finset.mem_filter] at hb
                  obtain ⟨hb, htl, hhd⟩ := hb
                  apply htl
                  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.head
                    ⟨b, hb, hf, rfl, rfl, Finset.mem_univ _, Finset.mem_univ _⟩ (Finset.mem_filter.mp hhd).2⟩
                have h1 := hInv Z ⟨v, hvZ⟩
                have hsubcl : SX Z ⊆ M.closure (Sv v) := by
                  rintro t ⟨y, hy, ht⟩
                  exact path Finset.univ v hg y (Finset.mem_filter.mp hy).2 ht
                have h2 := hmono _ _ hsubcl
                have h3 : rank M (M.closure (Sv v)) = rank M (Sv v) := by
                  have := M.eRk_closure_eq (Sv v)
                  rw [hrk, hrk] at this
                  exact_mod_cast this
                apply (hT3 v).isBase_of_eRk_ge (Set.toFinite _)
                rw [← Matroid.eRk_ground, hground, hrk, hrk]
                exact_mod_cast (show k ≤ rank M (Sv v) by omega)
              obtain ⟨a0, s0, hbad0⟩ := hex
              obtain ⟨X0, hX0⟩ := stepA a0 s0 hbad0
              have hP : ∃ n, ∃ a s X, Bad a s ∧ W (D'.tail a) (D'.head a) s X ∧ X.card = n :=
                ⟨_, a0, s0, X0, hbad0, hX0, rfl⟩
              obtain ⟨a, s, X, hbad, hW, hXc⟩ := Nat.find_spec hP
              have hmin : ∀ a' s' X', Bad a' s' → W (D'.tail a') (D'.head a') s' X' → X.card ≤ X'.card := by
                intro a' s' X' h1 h2
                rw [hXc]; exact Nat.find_min' hP ⟨a', s', X', h1, h2, rfl⟩
              obtain ⟨hXne, htight, hvX, huX, hsX⟩ := hW
              set Y := X.filter (fun y => Relation.ReflTransGen (R X) y (D'.head a)) with hY
              have hYX : Y ⊆ X := Finset.filter_subset _ _
              have hvY : D'.head a ∈ Y := Finset.mem_filter.mpr ⟨hvX, Relation.ReflTransGen.refl⟩
              have hfrY : fr Y ≤ fr X := by
                simp only [hfr]
                apply Finset.card_le_card
                intro b hb
                simp only [Digraph.enteringArcs, Finset.mem_filter] at hb ⊢
                obtain ⟨⟨hb, htl, hhd⟩, hf⟩ := hb
                have hhdX := hYX hhd
                refine ⟨⟨hb, ?_, hhdX⟩, hf⟩
                intro htX
                apply htl
                exact Finset.mem_filter.mpr ⟨htX, Relation.ReflTransGen.head
                  ⟨b, hb, hf, rfl, rfl, htX, hhdX⟩ (Finset.mem_filter.mp hhd).2⟩
              have hSXY : SX Y ⊆ SX X := by rintro t ⟨y, hy, ht⟩; exact ⟨y, hYX hy, ht⟩
              have h1 := hInv Y ⟨_, hvY⟩
              have h2 := hmono _ _ hSXY
              have hWY : W (D'.tail a) (D'.head a) s Y := by
                refine ⟨⟨_, hvY⟩, by omega, hvY, fun h => huX (hYX h), ?_⟩
                rw [hcleq _ _ hSXY (by omega)]; exact hsX
              have hYeq : Y = X := Finset.eq_of_subset_of_card_le hYX (hmin _ _ _ hbad hWY)
              have hreach : ∀ y ∈ X, Relation.ReflTransGen (R X) y (D'.head a) := by
                intro y hy; rw [← hYeq] at hy; exact (Finset.mem_filter.mp hy).2
              by_cases hg : ∀ b ∈ D'.arcs, (∀ s, b ∉ (T s).arcs) → D'.tail b ∈ X → D'.head b ∈ X →
                  Sv (D'.tail b) ⊆ M.closure (Sv (D'.head b))
              · apply hbad.2.2.2
                have hsub' : SX X ⊆ M.closure (Sv (D'.head a)) := by
                  rintro t ⟨y, hy, ht⟩; exact path X _ hg y (hreach y hy) ht
                exact M.closure_subset_closure_of_subset_closure hsub' hsX
              · simp only [not_forall] at hg
                obtain ⟨b, hb, hf, htb, hhb, hns⟩ := hg
                obtain ⟨t, ht, htn⟩ := Set.not_subset.mp hns
                have hbad' : Bad b t := ⟨hb, hf, ht, htn⟩
                obtain ⟨Y', hY'ne, htY', hvY', huY', htY'cl⟩ := stepA b t hbad'
                set Z := X ∩ Y' with hZ
                have hZne : Z.Nonempty := ⟨D'.head b, Finset.mem_inter.mpr ⟨hhb, hvY'⟩⟩
                have hUne : (X ∪ Y').Nonempty := ⟨D'.head b, Finset.mem_union_left _ hhb⟩
                have hd' : fr Z + fr (X ∪ Y') ≤ fr X + fr Y' := dsub (fun a => ∀ s, a ∉ (T s).arcs) X Y'
                have hSXU : SX (X ∪ Y') = SX X ∪ SX Y' := by
                  ext t'
                  simp only [hSX, Set.mem_setOf_eq, Set.mem_union, Finset.mem_union]
                  constructor
                  · rintro ⟨y, hy | hy, h⟩
                    · exact Or.inl ⟨y, hy, h⟩
                    · exact Or.inr ⟨y, hy, h⟩
                  · rintro (⟨y, hy, h⟩ | ⟨y, hy, h⟩)
                    · exact ⟨y, Or.inl hy, h⟩
                    · exact ⟨y, Or.inr hy, h⟩
                have hSXZ : SX Z ⊆ SX X ∩ SX Y' := by
                  rintro t' ⟨y, hy, h⟩
                  exact ⟨⟨y, (Finset.mem_inter.mp hy).1, h⟩, ⟨y, (Finset.mem_inter.mp hy).2, h⟩⟩
                have e1 := hInv Z hZne
                have e2 := hInv _ hUne
                have e3 := hsub (SX X) (SX Y')
                have e4 := hmono _ _ hSXZ
                rw [hSXU] at e2
                have hmod : rank M (SX X ∩ SX Y') + rank M (SX X ∪ SX Y') =
                    rank M (SX X) + rank M (SX Y') := by omega
                have hZt : fr Z + rank M (SX Z) = k := by omega
                have hZr : rank M (SX X ∩ SX Y') ≤ rank M (SX Z) := by omega
                have htX : rank M (insert t (SX X)) = rank M (SX X) := by
                  rw [Set.insert_eq_of_mem (hSvX _ _ htb ht)]
                have htI := claim21 _ _ t hmod htX ((hcl _ _).mp htY'cl)
                have hWZ : W (D'.tail b) (D'.head b) t Z := by
                  refine ⟨hZne, hZt, Finset.mem_inter.mpr ⟨hhb, hvY'⟩,
                    fun h => huY' (Finset.mem_inter.mp h).2, ?_⟩
                  rw [hcleq _ _ hSXZ hZr]
                  exact (hcl _ _).mpr htI
                have hlt : Z.card < X.card := by
                  apply Finset.card_lt_card
                  refine ⟨Finset.inter_subset_left, fun h => huY' ?_⟩
                  exact (Finset.mem_inter.mp (h htb)).2
                have := hmin _ _ _ hbad' hWZ
                omega
            have step : ∀ T, Inv T → (∃ v, ¬ M.IsBase {s | v ∈ (T s).verts}) →
                ∃ T', Inv T' ∧ μ T < μ T' := by
              intro T hT hb
              obtain ⟨a, s, h1, h2, h3, h4, h5, h6⟩ := exist T hT hb
              exact ext T hT a s h1 h2 h3 h4 h5 h6
            have bound : ∀ T : S → Arborescence D', μ T ≤ Fintype.card S * Fintype.card V := by
              intro T
              calc μ T ≤ ∑ _s : S, Fintype.card V :=
                    Finset.sum_le_sum (fun s _ => Finset.card_le_univ _)
                _ = _ := by simp
            have init : Inv (fun s => Arborescence.single D' (π s)) := by
              refine ⟨fun s => rfl, fun s s' _ => by simp [Arborescence.single], ?_, ?_⟩
              · intro v
                convert hind v using 1
                ext s; simp [Arborescence.single, eq_comm]
              · intro X hX
                have h := hconn X hX
                have e1 : ((D'.enteringArcs X).filter (fun a => ∀ s,
                    a ∉ (Arborescence.single D' (π s)).arcs)) = D'.enteringArcs X := by
                  apply Finset.filter_true_of_mem
                  intro a _ s; simp [Arborescence.single]
                have e2 : {s | ∃ v ∈ X, v ∈ (Arborescence.single D' (π s)).verts} = π ⁻¹' (X : Set V) := by
                  ext s; simp [Arborescence.single]
                rw [e1, e2]
                exact h
            have iter : ∀ n, ∀ T, Inv T → Fintype.card S * Fintype.card V - μ T = n →
                ∃ T : S → Arborescence D', IsBasicPacking D' π M T := by
              intro n
              induction n using Nat.strong_induction_on with
              | _ n ih =>
                intro T hT hn
                by_cases hb : ∃ v, ¬ M.IsBase {s | v ∈ (T s).verts}
                · obtain ⟨T', hT', hlt⟩ := step T hT hb
                  have h1 := bound T'
                  exact ih _ (by omega) T' hT' rfl
                · push_neg at hb
                  exact ⟨T, hT.1, hT.2.1, hb⟩
            exact iter _ _ init rfl
          have hrk : ∀ Q : Set S, M.eRk Q = (rank M Q : ℕ∞) := by
            intro Q
            unfold rank
            rw [ENat.coe_toNat]
            exact (Matroid.IsRkFinite.eRk_lt_top (M.isRkFinite_of_finite (Set.toFinite Q))).ne
          have hsumall : ∀ y : ArcVector D, arcSum D y D.arcs = ∑ a, y a := by
            intro y
            unfold arcSum
            exact Finset.sum_congr rfl (fun a _ => if_pos a.prop)
          -- every point of P forces π to be M-independent (counting over singletons)
          have hMind : ∀ x ∈ P, MIndependent π M := by
            intro x hx
            obtain ⟨hx1, hx2, hx3⟩ := hx
            set Sv : V → Finset S := fun v => Finset.univ.filter (fun s => π s = v) with hSv
            have hSvc : ∀ v, ((Sv v : Finset S) : Set S) = π ⁻¹' (({v} : Finset V) : Set V) := by
              intro v; ext s; simp [hSv]
            have hrkle : ∀ v, rank M (π ⁻¹' (({v} : Finset V) : Set V)) ≤ (Sv v).card := by
              intro v
              rw [← hSvc]
              have h1 := M.eRk_le_encard ((Sv v : Finset S) : Set S)
              rw [hrk, Set.encard_coe_eq_coe_finsetCard] at h1
              exact_mod_cast h1
            have hcardS : ∑ v, (Sv v).card = Fintype.card S := by
              rw [← Finset.card_univ]
              exact (Finset.card_eq_sum_card_fiberwise (f := π) (t := Finset.univ)
                (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))).symm
            have hsing : ∑ v, arcSum D x (D.enteringArcs {v}) ≤ arcSum D x D.arcs := by
              rw [hsumall]
              unfold arcSum
              rw [Finset.sum_comm]
              apply Finset.sum_le_sum
              intro a _
              calc ∑ v, (if a.val ∈ D.enteringArcs {v} then x a else 0)
                  ≤ ∑ v, (if D.head a.val = v then x a else 0) := by
                    apply Finset.sum_le_sum
                    intro v _
                    by_cases h : D.head a.val = v
                    · rw [if_pos h]; split_ifs
                      · exact le_rfl
                      · exact (hx1 a).1
                    · rw [if_neg h, if_neg]
                      simp [Digraph.enteringArcs, h]
                _ = x a := by simp
            have hk : ∀ v, (rank M Set.univ : ℝ) ≤ arcSum D x (D.enteringArcs {v}) +
                (rank M (π ⁻¹' (({v} : Finset V) : Set V)) : ℝ) :=
              fun v => hx2 {v} (Finset.singleton_nonempty v)
            have hsumk : (rank M Set.univ : ℝ) * Fintype.card V ≤
                ∑ v, arcSum D x (D.enteringArcs {v}) +
                  ∑ v, (rank M (π ⁻¹' (({v} : Finset V) : Set V)) : ℝ) := by
              rw [← Finset.sum_add_distrib]
              calc (rank M Set.univ : ℝ) * Fintype.card V = ∑ _v : V, (rank M Set.univ : ℝ) := by
                    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
                _ ≤ _ := Finset.sum_le_sum (fun v _ => hk v)
            have hge : (Fintype.card S : ℝ) ≤
                ∑ v, (rank M (π ⁻¹' (({v} : Finset V) : Set V)) : ℝ) := by linarith
            have hge' : Fintype.card S ≤ ∑ v, rank M (π ⁻¹' (({v} : Finset V) : Set V)) := by
              exact_mod_cast hge
            intro v
            by_contra hcon
            have hlt : rank M (π ⁻¹' (({v} : Finset V) : Set V)) < (Sv v).card := by
              rcases (hrkle v).lt_or_eq with h | h
              · exact h
              · exfalso; apply hcon
                have hfin : (π ⁻¹' ({v} : Set V)).Finite := Set.toFinite _
                rw [Matroid.indep_iff_eRk_eq_encard_of_finite hfin]
                have e1 : π ⁻¹' ({v} : Set V) = ((Sv v : Finset S) : Set S) := by
                  rw [hSvc, Finset.coe_singleton]
                rw [e1, Set.encard_coe_eq_coe_finsetCard, ← e1, hrk, ← Finset.coe_singleton, h]
            have := Finset.sum_lt_sum (s := Finset.univ) (fun w _ => hrkle w) ⟨v, Finset.mem_univ _, hlt⟩
            omega
          -- DEEP FACT 1 (Theorem 1.6 sufficiency, applied to the support of an integer point)
          have deep1 : ∀ x ∈ Z, ∃ T : S → Arborescence D, IsBasicPacking D π M T ∧ x = packingVector D T := by
            rintro x ⟨hxP, hxZ⟩
            have h01 : ∀ a, x a = 0 ∨ x a = 1 := by
              intro a
              obtain ⟨z, hz⟩ := hxZ a
              have h1 := hxP.1 a
              rw [hz] at h1 ⊢
              have : (0:ℤ) ≤ z := by exact_mod_cast h1.1
              have : z ≤ 1 := by exact_mod_cast h1.2
              interval_cases z <;> simp
            set F : Finset Arc := (D.arcs.attach.filter (fun a => x a = 1)).map
              (Function.Embedding.subtype _) with hF
            have hFsub : F ⊆ D.arcs := by
              intro a ha
              simp only [hF, Finset.mem_map, Finset.mem_filter, Function.Embedding.coe_subtype] at ha
              obtain ⟨b, _, rfl⟩ := ha
              exact b.prop
            have hmemF : ∀ a : {a // a ∈ D.arcs}, a.val ∈ F ↔ x a = 1 := by
              intro a
              simp only [hF, Finset.mem_map, Finset.mem_filter, Function.Embedding.coe_subtype,
                Finset.mem_attach, true_and]
              constructor
              · rintro ⟨b, hb, hba⟩
                have : b = a := Subtype.ext hba
                exact this ▸ hb
              · intro h; exact ⟨a, h, rfl⟩
            have hsumx : ∀ G : Finset Arc, arcSum D x G = ((F ∩ G).card : ℝ) := by
              intro G
              unfold arcSum
              calc _ = ∑ a ∈ D.arcs, (if a ∈ F ∩ G then (1:ℝ) else 0) := by
                    rw [← Finset.sum_coe_sort D.arcs]
                    apply Finset.sum_congr rfl
                    intro a _
                    have hm := hmemF a
                    by_cases h1 : a.val ∈ G <;> rcases h01 a with h | h <;>
                      simp [h, h1, Finset.mem_inter, hm]
                _ = ((F ∩ G).card : ℝ) := by
                    rw [Finset.sum_boole]
                    congr 2
                    ext a
                    simp only [Finset.mem_filter, Finset.mem_inter]
                    constructor
                    · intro h; exact h.2
                    · intro h; exact ⟨hFsub h.1, h⟩
            let D' : Digraph V Arc := ⟨D.tail, D.head, F⟩
            have hconn : MConnected D' π M := by
              intro X hX
              have h := hxP.2.1 X hX
              rw [hsumx] at h
              have hent : D'.enteringArcs X = F ∩ D.enteringArcs X := by
                ext a
                simp only [Digraph.enteringArcs, Finset.mem_filter, Finset.mem_inter, D']
                constructor
                · rintro ⟨h1, h2⟩; exact ⟨h1, hFsub h1, h2⟩
                · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
              have h' : rank M Set.univ ≤ (F ∩ D.enteringArcs X).card + rank M (π ⁻¹' (X : Set V)) := by
                exact_mod_cast h
              rw [hrk, hrk, Digraph.inDeg, hent]
              exact_mod_cast h'
            obtain ⟨T', hT'⟩ := thm16 D' (hMind x hxP) hconn
            let T : S → Arborescence D := fun s =>
              { verts := (T' s).verts, arcs := (T' s).arcs, root := (T' s).root,
                arcs_subset := (T' s).arcs_subset.trans hFsub,
                tail_mem := (T' s).tail_mem, head_mem := (T' s).head_mem,
                root_mem := (T' s).root_mem, root_inDeg := (T' s).root_inDeg,
                inDeg_one := (T' s).inDeg_one, reach := (T' s).reach }
            have hT : IsBasicPacking D π M T := ⟨hT'.1, hT'.2.1, hT'.2.2⟩
            refine ⟨T, hT, ?_⟩
            have hpv := easy T hT
            have hle : ∀ a ∈ (Finset.univ : Finset {a // a ∈ D.arcs}), packingVector D T a ≤ x a := by
              intro a _
              unfold packingVector
              split_ifs with h
              · obtain ⟨s, hs⟩ := h
                have : a.val ∈ F := (T' s).arcs_subset hs
                rw [hmemF] at this
                rw [this]
              · exact (hxP.1 a).1
            have heq : ∑ a, packingVector D T a = ∑ a, x a := by
              rw [← hsumall, ← hsumall, hpv.2.2, hxP.2.2]
            have := (Finset.sum_eq_sum_iff_of_le hle).mp heq
            funext a
            exact (this a (Finset.mem_univ _)).symm
          -- DEEP FACT 2 (integrality of the polyhedron)
          have deep2 : P ⊆ convexHull ℝ Z := by
            have hcont : ∀ F : Finset Arc, Continuous (fun x : ArcVector D => arcSum D x F) := by
              intro F
              unfold arcSum
              apply continuous_finset_sum
              intro a _
              split_ifs
              · exact continuous_apply a
              · exact continuous_const
            have hPclosed : IsClosed P := by
              have e : P = (⋂ a, {x : ArcVector D | 0 ≤ x a ∧ x a ≤ 1}) ∩ ((⋂ X : Finset V, ⋂ (_ : X.Nonempty),
                  {x : ArcVector D | (rank M Set.univ : ℝ) ≤ arcSum D x (D.enteringArcs X) +
                    (rank M (π ⁻¹' (X : Set V)) : ℝ)}) ∩
                  {x | arcSum D x D.arcs = (rank M Set.univ : ℝ) * Fintype.card V - Fintype.card S}) := by
                ext x
                simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, hPdef, packingPolyhedron]
              rw [e]
              refine IsClosed.inter (isClosed_iInter fun a => ?_)
                (IsClosed.inter (isClosed_iInter fun X => isClosed_iInter fun _ => ?_) ?_)
              · exact (isClosed_le continuous_const (continuous_apply a)).inter
                  (isClosed_le (continuous_apply a) continuous_const)
              · exact isClosed_le continuous_const ((hcont _).add continuous_const)
              · exact isClosed_eq (hcont _) continuous_const
            have hPcomp : IsCompact P := by
              apply (isCompact_Icc (a := (0 : ArcVector D)) (b := 1)).of_isClosed_subset hPclosed
              intro x hx
              exact ⟨fun a => (hx.1 a).1, fun a => (hx.1 a).2⟩
            have hZfin : Z.Finite := by
              apply (Set.Finite.pi (t := fun _ : {a // a ∈ D.arcs} => ({0, 1} : Set ℝ))
                (fun _ => Set.toFinite _)).subset
              intro x hx
              simp only [Set.mem_pi, Set.mem_univ, true_implies]
              intro a
              obtain ⟨z, hz⟩ := hx.2 a
              have h1 := hx.1.1 a
              rw [hz] at h1 ⊢
              have : (0:ℤ) ≤ z := by exact_mod_cast h1.1
              have : z ≤ 1 := by exact_mod_cast h1.2
              interval_cases z <;> simp
            have hext : P.extremePoints ℝ ⊆ Z := by
              intro x hxe
              have hx : x ∈ P := hxe.1
              refine ⟨hx, ?_⟩
              by_contra hnot
              push_neg at hnot
              obtain ⟨a0, ha0⟩ := hnot
              have hF0 : 0 < x a0 ∧ x a0 < 1 := by
                have h1 := hx.1 a0
                rcases h1.1.lt_or_eq with h | h
                · rcases h1.2.lt_or_eq with h' | h'
                  · exact ⟨h, h'⟩
                  · exact absurd (by rw [h']; simp) (ha0 1)
                · exact absurd (by rw [← h]; simp) (ha0 0)
              have core : ∃ d : ArcVector D, d ≠ 0 ∧ (∀ a, ¬(0 < x a ∧ x a < 1) → d a = 0) ∧
                  (∀ X : Finset V, X.Nonempty → arcSum D x (D.enteringArcs X) +
                    (rank M (π ⁻¹' (X : Set V)) : ℝ) = rank M Set.univ →
                    arcSum D d (D.enteringArcs X) = 0) ∧ arcSum D d D.arcs = 0 := by
                have hind := hMind x hx
                obtain ⟨hx1, hx2, hx3⟩ := hx
                obtain ⟨xs, hxs⟩ : ∃ xs : ({a // a ∈ D.arcs} → Prop) → ℝ,
                    ∀ (Q : {a // a ∈ D.arcs} → Prop) [DecidablePred Q], xs Q = ∑ a, if Q a then x a else 0 :=
                  ⟨fun Q => ∑ a, if Q a then x a else 0, fun Q _ => Finset.sum_congr rfl (fun a _ => by congr)⟩
                have hent : ∀ (y : ArcVector D) (X : Finset V), arcSum D y (D.enteringArcs X) =
                    ∑ a : {a // a ∈ D.arcs}, if (D.tail a.val ∉ X ∧ D.head a.val ∈ X) then y a else 0 := by
                  intro y X; unfold arcSum; apply Finset.sum_congr rfl; intro a _
                  simp [Digraph.enteringArcs, a.prop]
                have hxsc : ∀ Q Q' : {a // a ∈ D.arcs} → Prop, (∀ a, Q a ↔ Q' a) → xs Q = xs Q' := by
                  intro Q Q' h
                  have : Q = Q' := funext fun a => propext (h a)
                  rw [this]
                obtain ⟨tight, htight⟩ : ∃ tight : Finset V → Prop, ∀ X, tight X ↔ (X.Nonempty ∧
                    xs (fun a => D.tail a.val ∉ X ∧ D.head a.val ∈ X) + (rank M (π ⁻¹' (X : Set V)) : ℝ)
                      = rank M Set.univ) := ⟨_, fun X => Iff.rfl⟩
                have hcons : ∀ X : Finset V, X.Nonempty → (rank M Set.univ : ℝ) ≤
                    xs (fun a => D.tail a.val ∉ X ∧ D.head a.val ∈ X) + (rank M (π ⁻¹' (X : Set V)) : ℝ) := by
                  intro X hX; have := hx2 X hX; rw [hent, ← hxs] at this; exact this
                -- S1: head sums
                have hrv : ∀ v, (rank M (π ⁻¹' ({v} : Set V)) : ℝ) =
                    ((Finset.univ.filter (fun s => π s = v)).card : ℝ) := by
                  intro v
                  have h1 := (hind v).eRk_eq_encard
                  have e1 : π ⁻¹' ({v} : Set V) = ((Finset.univ.filter (fun s => π s = v) : Finset S) : Set S) := by
                    ext s; simp
                  rw [hrk, e1, Set.encard_coe_eq_coe_finsetCard, ← e1] at h1
                  exact_mod_cast h1
                have hsumr : ∑ v, (rank M (π ⁻¹' ({v} : Set V)) : ℝ) = Fintype.card S := by
                  simp_rw [hrv]
                  have := (Finset.card_eq_sum_card_fiberwise (f := π) (s := Finset.univ) (t := Finset.univ)
                    (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)))
                  rw [Finset.card_univ] at this
                  exact_mod_cast this.symm
                have hH : ∀ v, xs (fun a => D.head a.val = v) =
                    (rank M Set.univ : ℝ) - rank M (π ⁻¹' ({v} : Set V)) := by
                  have hle : ∀ v, (rank M Set.univ : ℝ) - rank M (π ⁻¹' ({v} : Set V)) ≤
                      xs (fun a => D.head a.val = v) := by
                    intro v
                    have h1 := hcons {v} (Finset.singleton_nonempty v)
                    rw [Finset.coe_singleton] at h1
                    have h2 : xs (fun a => D.tail a.val ∉ ({v} : Finset V) ∧ D.head a.val ∈ ({v} : Finset V))
                        ≤ xs (fun a => D.head a.val = v) := by
                      rw [hxs, hxs]; apply Finset.sum_le_sum; intro a _
                      by_cases h : D.head a.val = v
                      · simp only [h, Finset.mem_singleton, and_true, if_true]
                        split_ifs <;> linarith [(hx1 a).1]
                      · simp [h]
                    linarith
                  have hsum : ∑ v, xs (fun a => D.head a.val = v) = ∑ a, x a := by
                    simp_rw [hxs]
                    rw [Finset.sum_comm]
                    apply Finset.sum_congr rfl; intro a _
                    simp
                  have htot : ∑ v, ((rank M Set.univ : ℝ) - rank M (π ⁻¹' ({v} : Set V))) = ∑ a, x a := by
                    rw [Finset.sum_sub_distrib, hsumr, ← hsumall, hx3]
                    simp [Finset.sum_const, Finset.card_univ, mul_comm]
                  have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
                    (f := fun v => xs (fun a => D.head a.val = v) -
                      ((rank M Set.univ : ℝ) - rank M (π ⁻¹' ({v} : Set V))))
                    (fun v _ => sub_nonneg.mpr (hle v))).mp (by rw [Finset.sum_sub_distrib, hsum, htot, sub_self])
                  intro v
                  have := hz v (Finset.mem_univ v)
                  linarith
                -- S2: induced sums of tight sets are integers
                have hsplit : ∀ X : Finset V, xs (fun a => D.tail a.val ∈ X ∧ D.head a.val ∈ X) +
                    xs (fun a => D.tail a.val ∉ X ∧ D.head a.val ∈ X) =
                    ∑ v ∈ X, xs (fun a => D.head a.val = v) := by
                  intro X
                  simp_rw [hxs]
                  rw [← Finset.sum_add_distrib, Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro a _
                  by_cases h1 : D.tail a.val ∈ X <;> by_cases h2 : D.head a.val ∈ X <;> simp [h1, h2]
                have hindInt : ∀ X, tight X → ∃ z : ℤ,
                    xs (fun a => D.tail a.val ∈ X ∧ D.head a.val ∈ X) = z := by
                  intro X hX
                  rw [htight] at hX
                  have h1 := hsplit X
                  simp_rw [hH] at h1
                  refine ⟨∑ v ∈ X, ((rank M Set.univ : ℤ) - rank M (π ⁻¹' ({v} : Set V))) -
                    ((rank M Set.univ : ℤ) - rank M (π ⁻¹' (X : Set V))), ?_⟩
                  push_cast
                  linarith [hX.2]
                -- S3: intersection closure
                have hinter : ∀ X Y, tight X → tight Y → (X ∩ Y).Nonempty → tight (X ∩ Y) := by
                  intro X Y hX hY hXY
                  rw [htight] at hX hY ⊢
                  refine ⟨hXY, ?_⟩
                  have hsub : (rank M (π ⁻¹' ((X ∩ Y : Finset V) : Set V)) : ℝ) +
                      rank M (π ⁻¹' ((X ∪ Y : Finset V) : Set V)) ≤
                      rank M (π ⁻¹' (X : Set V)) + rank M (π ⁻¹' (Y : Set V)) := by
                    have h := M.eRk_inter_add_eRk_union_le (π ⁻¹' (X : Set V)) (π ⁻¹' (Y : Set V))
                    rw [← Set.preimage_inter, ← Set.preimage_union, ← Finset.coe_inter, ← Finset.coe_union,
                      hrk, hrk, hrk, hrk] at h
                    exact_mod_cast h
                  have hent2 : xs (fun a => D.tail a.val ∉ X ∩ Y ∧ D.head a.val ∈ X ∩ Y) +
                      xs (fun a => D.tail a.val ∉ X ∪ Y ∧ D.head a.val ∈ X ∪ Y) ≤
                      xs (fun a => D.tail a.val ∉ X ∧ D.head a.val ∈ X) +
                      xs (fun a => D.tail a.val ∉ Y ∧ D.head a.val ∈ Y) := by
                    simp_rw [hxs]
                    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                    apply Finset.sum_le_sum; intro a _
                    have := (hx1 a).1
                    by_cases h1 : D.tail a.val ∈ X <;> by_cases h2 : D.tail a.val ∈ Y <;>
                      by_cases h3 : D.head a.val ∈ X <;> by_cases h4 : D.head a.val ∈ Y <;>
                      simp [h1, h2, h3, h4] <;> linarith
                  have hc1 := hcons (X ∩ Y) hXY
                  have hc2 := hcons (X ∪ Y) (hX.1.mono Finset.subset_union_left)
                  linarith [hX.2, hY.2]
                -- S4: unions of tight families
                have hunion : ∀ n : ℕ, ∀ 𝒵 : Finset (Finset V), 𝒵.card ≤ n → (∀ Z ∈ 𝒵, tight Z) →
                    ∃ z : ℤ, xs (fun a => ∃ Z ∈ 𝒵, D.tail a.val ∈ Z ∧ D.head a.val ∈ Z) = z := by
                  intro n
                  induction n with
                  | zero =>
                    intro 𝒵 h _
                    have : 𝒵 = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp h)
                    subst this
                    exact ⟨0, by rw [hxs]; simp⟩
                  | succ n ih =>
                    intro 𝒵 hcard hT
                    rcases 𝒵.eq_empty_or_nonempty with h | ⟨Z0, hZ0⟩
                    · subst h; exact ⟨0, by rw [hxs]; simp⟩
                    set 𝒵' := 𝒵.erase Z0
                    set 𝒲 := (𝒵'.filter (fun Z => (Z0 ∩ Z).Nonempty)).image (fun Z => Z0 ∩ Z)
                    have hc' : 𝒵'.card ≤ n := by
                      have : 𝒵'.card = 𝒵.card - 1 := Finset.card_erase_of_mem hZ0
                      omega
                    have hcW : 𝒲.card ≤ n :=
                      (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans hc'
                    have hT' : ∀ Z ∈ 𝒵', tight Z := fun Z hZ => hT Z (Finset.mem_of_mem_erase hZ)
                    have hTW : ∀ W ∈ 𝒲, tight W := by
                      intro W hW
                      simp only [𝒲, Finset.mem_image, Finset.mem_filter] at hW
                      obtain ⟨Z, ⟨hZ, hne⟩, rfl⟩ := hW
                      exact hinter _ _ (hT Z0 hZ0) (hT' Z hZ) hne
                    obtain ⟨z0, hz0⟩ := hindInt Z0 (hT Z0 hZ0)
                    obtain ⟨z1, hz1⟩ := ih 𝒵' hc' hT'
                    obtain ⟨z2, hz2⟩ := ih 𝒲 hcW hTW
                    refine ⟨z0 + z1 - z2, ?_⟩
                    push_cast
                    rw [← hz0, ← hz1, ← hz2]
                    simp_rw [hxs]
                    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl; intro a _
                    have i1 : (∃ Z ∈ 𝒵, D.tail a.val ∈ Z ∧ D.head a.val ∈ Z) ↔
                        (D.tail a.val ∈ Z0 ∧ D.head a.val ∈ Z0) ∨
                        (∃ Z ∈ 𝒵', D.tail a.val ∈ Z ∧ D.head a.val ∈ Z) := by
                      constructor
                      · rintro ⟨Z, hZ, h⟩
                        by_cases hz : Z = Z0
                        · subst hz; exact Or.inl h
                        · exact Or.inr ⟨Z, Finset.mem_erase.mpr ⟨hz, hZ⟩, h⟩
                      · rintro (h | ⟨Z, hZ, h⟩)
                        · exact ⟨Z0, hZ0, h⟩
                        · exact ⟨Z, Finset.mem_of_mem_erase hZ, h⟩
                    have i2 : (∃ W ∈ 𝒲, D.tail a.val ∈ W ∧ D.head a.val ∈ W) ↔
                        (D.tail a.val ∈ Z0 ∧ D.head a.val ∈ Z0) ∧
                        (∃ Z ∈ 𝒵', D.tail a.val ∈ Z ∧ D.head a.val ∈ Z) := by
                      constructor
                      · rintro ⟨W, hW, h⟩
                        simp only [𝒲, Finset.mem_image, Finset.mem_filter] at hW
                        obtain ⟨Z, ⟨hZ, _⟩, rfl⟩ := hW
                        simp only [Finset.mem_inter] at h
                        exact ⟨⟨h.1.1, h.2.1⟩, Z, hZ, h.1.2, h.2.2⟩
                      · rintro ⟨h0, Z, hZ, h⟩
                        refine ⟨Z0 ∩ Z, ?_, ?_⟩
                        · simp only [𝒲, Finset.mem_image, Finset.mem_filter]
                          exact ⟨Z, ⟨hZ, ⟨D.head a.val, Finset.mem_inter.mpr ⟨h0.2, h.2⟩⟩⟩, rfl⟩
                        · simp only [Finset.mem_inter]; exact ⟨⟨h0.1, h.1⟩, h0.2, h.2⟩
                    rw [if_congr i1 rfl rfl, if_congr i2 rfl rfl]
                    by_cases p0 : (D.tail a.val ∈ Z0 ∧ D.head a.val ∈ Z0) <;>
                      by_cases p1 : (∃ Z ∈ 𝒵', D.tail a.val ∈ Z ∧ D.head a.val ∈ Z) <;>
                      simp only [p0, p1, true_or, or_true, or_false, false_or, and_true, true_and,
                        and_false, false_and, if_true, if_false] <;> ring
                -- S5: classes
                set F : Finset {a // a ∈ D.arcs} := Finset.univ.filter (fun a => 0 < x a ∧ x a < 1) with hFdef
                have hmemF : ∀ a, a ∈ F ↔ (0 < x a ∧ x a < 1) := by intro a; simp [hFdef]
                have hFint : ∀ (Q : {a // a ∈ D.arcs} → Prop) [DecidablePred Q],
                    ∃ z : ℤ, xs Q = ∑ a ∈ F.filter Q, x a + z := by
                  intro Q _
                  refine ⟨((Finset.univ.filter (fun a => a ∉ F ∧ Q a ∧ x a = 1)).card : ℤ), ?_⟩
                  rw [hxs]
                  have e : ∀ a, (if Q a then x a else 0) = (if a ∈ F.filter Q then x a else 0) +
                      (if (a ∉ F ∧ Q a ∧ x a = 1) then 1 else 0) := by
                    intro a
                    by_cases hq : Q a
                    · by_cases hf : a ∈ F
                      · simp [hq, hf]
                      · have h01 : x a = 0 ∨ x a = 1 := by
                          have hf' := hf
                          rw [hmemF] at hf'
                          have := hx1 a
                          by_contra h; push_neg at h
                          exact hf' ⟨lt_of_le_of_ne this.1 (Ne.symm h.1), lt_of_le_of_ne this.2 h.2⟩
                        rcases h01 with h | h <;> simp [hq, hf, h]
                    · simp [hq]
                  rw [Finset.sum_congr rfl (fun a _ => e a), Finset.sum_add_distrib, Finset.sum_ite_mem,
                    Finset.univ_inter]
                  simp
                have hcard2 : ∀ C : Finset {a // a ∈ D.arcs}, C ⊆ F → C.Nonempty →
                    (∃ z : ℤ, ∑ a ∈ C, x a = z) → 2 ≤ C.card := by
                  rintro C hC hne ⟨z, hz⟩
                  by_contra hlt
                  have h1 : C.card = 1 := by have := hne.card_pos; omega
                  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
                  rw [Finset.sum_singleton] at hz
                  have ha := (hmemF a).mp (hC (Finset.mem_singleton_self a))
                  rw [hz] at ha
                  have h1 : (0:ℤ) < z := by exact_mod_cast ha.1
                  have h2 : z < 1 := by exact_mod_cast ha.2
                  omega
                set 𝒯 : Finset (Finset V) := Finset.univ.filter tight with h𝒯
                set κ : {a // a ∈ D.arcs} → Finset (Finset V) :=
                  fun a => 𝒯.filter (fun X => D.tail a.val ∈ X ∧ D.head a.val ∈ X) with hκ
                have hmemκ : ∀ a X, X ∈ κ a ↔ tight X ∧ D.tail a.val ∈ X ∧ D.head a.val ∈ X := by
                  intro a X; simp [hκ, h𝒯]
                have hinterF : ∀ (σ : Finset (Finset V)) (w : V), σ.Nonempty → (∀ X ∈ σ, tight X ∧ w ∈ X) →
                    tight (Finset.univ.filter (fun v => ∀ X ∈ σ, v ∈ X)) := by
                  intro σ w
                  induction σ using Finset.induction_on with
                  | empty => intro h; exact absurd h Finset.not_nonempty_empty
                  | insert X τ hXτ ih =>
                    intro _ h
                    rcases τ.eq_empty_or_nonempty with he | hne
                    · subst he
                      have e : (Finset.univ.filter (fun v => ∀ X' ∈ insert X (∅ : Finset (Finset V)), v ∈ X'))
                          = X := by
                        ext v; simp
                      rw [e]; exact (h X (Finset.mem_insert_self X _)).1
                    · have e : (Finset.univ.filter (fun v => ∀ X' ∈ insert X τ, v ∈ X')) =
                          X ∩ Finset.univ.filter (fun v => ∀ X' ∈ τ, v ∈ X') := by
                        ext v; simp
                      rw [e]
                      have hτ := ih hne (fun X' hX' => h X' (Finset.mem_insert_of_mem hX'))
                      refine hinter _ _ (h X (Finset.mem_insert_self X _)).1 hτ ⟨w, ?_⟩
                      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
                      exact ⟨(h X (Finset.mem_insert_self X _)).2,
                        fun X' hX' => (h X' (Finset.mem_insert_of_mem hX')).2⟩
                have hclassInt : ∀ σ ∈ F.image κ, σ ≠ ∅ →
                    ∃ z : ℤ, ∑ a ∈ F.filter (fun a => κ a = σ), x a = z := by
                  intro σ hσ hne
                  obtain ⟨a1, ha1F, ha1σ⟩ := Finset.mem_image.mp hσ
                  have hσT : ∀ X ∈ σ, tight X ∧ D.tail a1.val ∈ X ∧ D.head a1.val ∈ X := by
                    intro X hX; rw [← ha1σ] at hX; exact (hmemκ a1 X).mp hX
                  set Y := Finset.univ.filter (fun v => ∀ X ∈ σ, v ∈ X) with hY
                  have hYt : tight Y := hinterF σ (D.tail a1.val) (Finset.nonempty_iff_ne_empty.mpr hne)
                    (fun X hX => ⟨(hσT X hX).1, (hσT X hX).2.1⟩)
                  set 𝒰 := 𝒯 \ σ with h𝒰
                  have h𝒰t : ∀ X ∈ 𝒰, tight X := by
                    intro X hX; simp [h𝒰, h𝒯] at hX; exact hX.1
                  have hiff : ∀ a, κ a = σ ↔ ((D.tail a.val ∈ Y ∧ D.head a.val ∈ Y) ∧
                      ¬ ∃ X ∈ 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X) := by
                    intro a
                    constructor
                    · intro h
                      refine ⟨?_, ?_⟩
                      · simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and]
                        constructor
                        · intro X hX; rw [← h] at hX; exact ((hmemκ a X).mp hX).2.1
                        · intro X hX; rw [← h] at hX; exact ((hmemκ a X).mp hX).2.2
                      · rintro ⟨X, hX, hin⟩
                        simp only [h𝒰, Finset.mem_sdiff, h𝒯, Finset.mem_filter, Finset.mem_univ,
                          true_and] at hX
                        apply hX.2; rw [← h]; exact (hmemκ a X).mpr ⟨hX.1, hin⟩
                    · rintro ⟨hYa, hU⟩
                      ext X
                      rw [hmemκ]
                      constructor
                      · rintro ⟨hXt, hin⟩
                        by_contra hXσ
                        exact hU ⟨X, by simp [h𝒰, h𝒯, hXt, hXσ], hin⟩
                      · intro hX
                        simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hYa
                        exact ⟨(hσT X hX).1, hYa.1 X hX, hYa.2 X hX⟩
                  obtain ⟨z1, hz1⟩ := hFint (fun a => (D.tail a.val ∈ Y ∧ D.head a.val ∈ Y) ∧
                    ¬ ∃ X ∈ 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X)
                  obtain ⟨z2, hz2⟩ := hunion _ (insert Y 𝒰) le_rfl (by
                    intro X hX
                    rcases Finset.mem_insert.mp hX with h | h
                    · rw [h]; exact hYt
                    · exact h𝒰t X h)
                  obtain ⟨z3, hz3⟩ := hunion _ 𝒰 le_rfl h𝒰t
                  refine ⟨z2 - z3 - z1, ?_⟩
                  rw [Finset.filter_congr (fun a _ => hiff a)]
                  have e : xs (fun a => (D.tail a.val ∈ Y ∧ D.head a.val ∈ Y) ∧
                      ¬ ∃ X ∈ 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X) =
                      xs (fun a => ∃ X ∈ insert Y 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X) -
                      xs (fun a => ∃ X ∈ 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X) := by
                    rw [hxs, hxs, hxs, ← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl; intro a _
                    have i1 : (∃ X ∈ insert Y 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X) ↔
                        (D.tail a.val ∈ Y ∧ D.head a.val ∈ Y) ∨
                        (∃ X ∈ 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X) := Finset.exists_mem_insert _ _ _
                    rw [if_congr i1 rfl rfl]
                    by_cases p0 : (D.tail a.val ∈ Y ∧ D.head a.val ∈ Y) <;>
                      by_cases p1 : (∃ X ∈ 𝒰, D.tail a.val ∈ X ∧ D.head a.val ∈ X) <;>
                      simp only [p0, p1, true_or, or_true, or_false, false_or, not_true, not_false_eq_true,
                        and_true, true_and, and_false, false_and, if_true, if_false] <;> ring
                  rw [e, hz2, hz3] at hz1
                  push_cast
                  linarith
                have hheadInt : ∀ v, ∃ z : ℤ, ∑ a ∈ F.filter (fun a => D.head a.val = v), x a = z := by
                  intro v
                  obtain ⟨z1, hz1⟩ := hFint (fun a => D.head a.val = v)
                  refine ⟨((rank M Set.univ : ℤ) - rank M (π ⁻¹' ({v} : Set V))) - z1, ?_⟩
                  rw [hH] at hz1
                  push_cast; linarith
                -- S6: counting and the kernel vector
                set ι := F.image κ with hι
                set Hs := F.image (fun a => D.head a.val) with hHs
                have ha0F : a0 ∈ F := (hmemF a0).mpr hF0
                have hv0 : D.head a0.val ∈ Hs := Finset.mem_image_of_mem _ ha0F
                have hcountι : 2 * ι.card ≤ F.card + 1 := by
                  have h1 := Finset.card_eq_sum_card_image κ F
                  have h2 : ∀ σ ∈ ι, 2 ≤ (F.filter (fun a => κ a = σ)).card + (if σ = ∅ then 1 else 0) := by
                    intro σ hσ
                    have hne : (F.filter (fun a => κ a = σ)).Nonempty := by
                      obtain ⟨a, ha, h⟩ := Finset.mem_image.mp hσ
                      exact ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩⟩
                    by_cases he : σ = ∅
                    · rw [if_pos he]; have := hne.card_pos; omega
                    · rw [if_neg he]
                      exact (hcard2 _ (Finset.filter_subset _ _) hne (hclassInt σ hσ he)).trans
                        (Nat.le_add_right _ _)
                  have h3 : ∑ σ ∈ ι, (if σ = ∅ then 1 else 0) ≤ 1 := by
                    rw [Finset.sum_ite_eq']; split_ifs <;> omega
                  have h4 := Finset.sum_le_sum h2
                  rw [Finset.sum_add_distrib, ← h1] at h4
                  simp only [Finset.sum_const, smul_eq_mul] at h4
                  omega
                have hcountH : 2 * Hs.card ≤ F.card := by
                  have h1 := Finset.card_eq_sum_card_image (fun a => D.head a.val) F
                  have h2 : ∀ v ∈ Hs, 2 ≤ (F.filter (fun a => D.head a.val = v)).card := by
                    intro v hv
                    obtain ⟨a, ha, h⟩ := Finset.mem_image.mp hv
                    exact hcard2 _ (Finset.filter_subset _ _) ⟨a, Finset.mem_filter.mpr ⟨ha, h⟩⟩ (hheadInt v)
                  have h4 := Finset.sum_le_sum h2
                  rw [← h1] at h4
                  simp only [Finset.sum_const, smul_eq_mul] at h4
                  omega
                let Mtx : Matrix ({σ // σ ∈ ι} ⊕ {v // v ∈ Hs.erase (D.head a0.val)}) {a // a ∈ F} ℝ :=
                  fun c a => Sum.elim (fun σ => if κ a.val = σ.val then (1:ℝ) else 0)
                    (fun v => if D.head a.val.val = v.val then (1:ℝ) else 0) c
                have hker : LinearMap.ker (Matrix.mulVecLin Mtx) ≠ ⊥ := by
                  apply LinearMap.ker_ne_bot_of_finrank_lt
                  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
                    Fintype.card_coe, Fintype.card_coe, Fintype.card_coe, Finset.card_erase_of_mem hv0]
                  have := Finset.card_pos.mpr ⟨_, hv0⟩
                  omega
                obtain ⟨d, hdker, hdne⟩ := (Submodule.ne_bot_iff _).mp hker
                rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hdker
                have K1 : ∀ σ ∈ ι, ∑ a : {a // a ∈ F}, (if κ a.val = σ then d a else 0) = 0 := by
                  intro σ hσ
                  have := congrFun hdker (Sum.inl ⟨σ, hσ⟩)
                  simpa [Matrix.mulVec, dotProduct, Mtx] using this
                have K2 : ∀ v ∈ Hs.erase (D.head a0.val),
                    ∑ a : {a // a ∈ F}, (if D.head a.val.val = v then d a else 0) = 0 := by
                  intro v hv
                  have := congrFun hdker (Sum.inr ⟨v, hv⟩)
                  simpa [Matrix.mulVec, dotProduct, Mtx] using this
                set d' : ArcVector D := fun a => if h : a ∈ F then d ⟨a, h⟩ else 0 with hd'
                have hd'F : ∀ a, a ∉ F → d' a = 0 := by intro a ha; simp [hd', ha]
                have htr : ∀ (Q : {a // a ∈ D.arcs} → Prop) [DecidablePred Q],
                    ∑ a : {a // a ∈ F}, (if Q a.val then d a else 0) = ∑ a, (if Q a then d' a else 0) := by
                  intro Q _
                  have e1 : ∀ a : {a // a ∈ F}, (if Q a.val then d a else 0) =
                      (fun b => if Q b then d' b else 0) a.val := by
                    intro a; simp [hd', a.prop]
                  rw [Finset.sum_congr rfl (fun a _ => e1 a),
                    Finset.sum_coe_sort F (fun b => if Q b then d' b else 0)]
                  apply Finset.sum_subset (Finset.subset_univ _)
                  intro a _ ha; simp [hd'F a ha]
                have K1u : ∀ σ ∈ ι, ∑ a, (if κ a = σ then d' a else 0) = 0 := by
                  intro σ hσ; rw [← htr]; exact K1 σ hσ
                have K2u' : ∀ v ∈ Hs.erase (D.head a0.val), ∑ a, (if D.head a.val = v then d' a else 0) = 0 := by
                  intro v hv; rw [← htr]; exact K2 v hv
                have hT1 : ∑ a, d' a = ∑ σ ∈ ι, ∑ a, (if κ a = σ then d' a else 0) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro a _
                  by_cases ha : a ∈ F
                  · have : κ a ∈ ι := Finset.mem_image_of_mem _ ha
                    simp [this]
                  · simp [hd'F a ha]
                have hT0 : ∑ a, d' a = 0 := by rw [hT1]; exact Finset.sum_eq_zero K1u
                have hT2 : ∑ a, d' a = ∑ v ∈ Hs, ∑ a, (if D.head a.val = v then d' a else 0) := by
                  rw [Finset.sum_comm]
                  apply Finset.sum_congr rfl; intro a _
                  by_cases ha : a ∈ F
                  · have : D.head a.val ∈ Hs := Finset.mem_image_of_mem _ ha
                    simp [this]
                  · simp [hd'F a ha]
                have K2u : ∀ v, ∑ a, (if D.head a.val = v then d' a else 0) = 0 := by
                  intro v
                  by_cases hv : v ∈ Hs
                  · by_cases hv0' : v = D.head a0.val
                    · have h := hT2
                      rw [hT0, ← Finset.add_sum_erase _ _ hv0, Finset.sum_eq_zero K2u', add_zero] at h
                      rw [hv0']; exact h.symm
                    · exact K2u' v (Finset.mem_erase.mpr ⟨hv0', hv⟩)
                  · apply Finset.sum_eq_zero; intro a _
                    split_ifs with h
                    · apply hd'F; intro ha; exact hv (h ▸ Finset.mem_image_of_mem _ ha)
                    · rfl
                have hver : ∀ X : Finset V, tight X →
                    ∑ a, (if (D.tail a.val ∉ X ∧ D.head a.val ∈ X) then d' a else 0) = 0 := by
                  intro X hX
                  have e1 : ∑ a, (if (D.tail a.val ∉ X ∧ D.head a.val ∈ X) then d' a else 0) =
                      ∑ a, (if D.head a.val ∈ X then d' a else 0) -
                      ∑ a, (if (D.tail a.val ∈ X ∧ D.head a.val ∈ X) then d' a else 0) := by
                    rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro a _
                    by_cases h1 : D.tail a.val ∈ X <;> by_cases h2 : D.head a.val ∈ X <;> simp [h1, h2]
                  have e2 : ∑ a, (if D.head a.val ∈ X then d' a else 0) =
                      ∑ v ∈ X, ∑ a, (if D.head a.val = v then d' a else 0) := by
                    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
                    simp
                  have e3 : ∑ a, (if (D.tail a.val ∈ X ∧ D.head a.val ∈ X) then d' a else 0) =
                      ∑ σ ∈ ι.filter (fun σ => X ∈ σ), ∑ a, (if κ a = σ then d' a else 0) := by
                    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _
                    by_cases ha : a ∈ F
                    · have hκι : κ a ∈ ι := Finset.mem_image_of_mem _ ha
                      have hi : (D.tail a.val ∈ X ∧ D.head a.val ∈ X) ↔ κ a ∈ ι.filter (fun σ => X ∈ σ) := by
                        rw [Finset.mem_filter]
                        constructor
                        · intro h; exact ⟨hκι, (hmemκ a X).mpr ⟨hX, h⟩⟩
                        · intro h; exact ((hmemκ a X).mp h.2).2
                      rw [Finset.sum_ite_eq]
                      exact if_congr hi rfl rfl
                    · simp [hd'F a ha]
                  rw [e1, e2, e3, Finset.sum_eq_zero (fun v _ => K2u v),
                    Finset.sum_eq_zero (fun σ hσ => K1u σ (Finset.mem_filter.mp hσ).1), sub_zero]
                refine ⟨d', ?_, ?_, ?_, ?_⟩
                · intro h; apply hdne; funext a
                  have := congrFun h a.val
                  simpa [hd', a.prop] using this
                · intro a ha; exact hd'F a (fun h => ha ((hmemF a).mp h))
                · intro X hX h
                  rw [hent]
                  apply hver
                  rw [htight]; refine ⟨hX, ?_⟩; rw [hxs]; rw [hent] at h; exact h
                · rw [hsumall]; exact hT0
              obtain ⟨d, hd0, hdF, hdT, hdA⟩ := core
              have hlin1 : ∀ (t : ℝ) F, arcSum D (x + t • d) F = arcSum D x F + t * arcSum D d F := by
                intro t F; have := hlin x d 1 t F; rw [one_smul, one_mul] at this; exact this
              have hev : ∀ᶠ t in nhds (0:ℝ), x + t • d ∈ P := by
                have e1 : ∀ᶠ t in nhds (0:ℝ), ∀ a, 0 ≤ (x + t • d) a ∧ (x + t • d) a ≤ 1 := by
                  rw [Filter.eventually_all]
                  intro a
                  by_cases hda : d a = 0
                  · exact Filter.Eventually.of_forall (fun t => by simp [hda]; exact hx.1 a)
                  · have hFa : 0 < x a ∧ x a < 1 := by by_contra h; exact hda (hdF a h)
                    have hc : Continuous (fun t : ℝ => x a + t * d a) := by fun_prop
                    have := hc.tendsto 0
                    simp only [zero_mul, add_zero] at this
                    filter_upwards [this.eventually (Ioo_mem_nhds hFa.1 hFa.2)] with t ht
                    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
                    exact ⟨ht.1.le, ht.2.le⟩
                have e2 : ∀ᶠ t in nhds (0:ℝ), ∀ X : Finset V, X.Nonempty → (rank M Set.univ : ℝ) ≤
                    arcSum D (x + t • d) (D.enteringArcs X) + (rank M (π ⁻¹' (X : Set V)) : ℝ) := by
                  rw [Filter.eventually_all]
                  intro X
                  by_cases hX : X.Nonempty
                  · have h2 := hx.2.1 X hX
                    rcases h2.lt_or_eq with h | h
                    · have hc : Continuous (fun t : ℝ => arcSum D x (D.enteringArcs X) +
                          t * arcSum D d (D.enteringArcs X) + (rank M (π ⁻¹' (X : Set V)) : ℝ)) := by
                        fun_prop
                      have := hc.tendsto 0
                      simp only [zero_mul, add_zero] at this
                      filter_upwards [this.eventually (lt_mem_nhds h)] with t ht _
                      rw [hlin1]; exact ht.le
                    · have h0 := hdT X hX h.symm
                      exact Filter.Eventually.of_forall (fun t _ => by rw [hlin1, h0]; linarith)
                  · exact Filter.Eventually.of_forall (fun t h => absurd h hX)
                filter_upwards [e1, e2] with t h1 h2
                exact ⟨h1, h2, by rw [hlin1, hdA, mul_zero, add_zero]; exact hx.2.2⟩
              obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
              have hp : x + (ε/2) • d ∈ P := hball (by
                rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith)
              have hm : x + (-(ε/2)) • d ∈ P := hball (by
                rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by linarith)]; linarith)
              have hseg : x ∈ openSegment ℝ (x + (ε/2) • d) (x + (-(ε/2)) • d) :=
                ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, by
                  ext a; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring⟩
              have h3 := hxe.2 hp hm hseg
              apply hd0
              have h4 : (ε/2) • d = 0 := by
                have := congrArg (fun y => y - x) h3; simpa using this
              exact (smul_eq_zero.mp h4).resolve_left (by linarith)
            intro x hx
            rw [← closure_convexHull_extremePoints hPcomp hconv] at hx
            exact closure_minimal (convexHull_mono hext) (hZfin.isClosed_convexHull ℝ) hx
          have hint : IntegralPolyhedron P := by
            apply Set.Subset.antisymm deep2
            exact convexHull_min (fun x hx => hx.1) hconv
          refine ⟨⟨fun ⟨T, hT⟩ => ⟨_, easy T hT⟩, fun ⟨x, hx⟩ => ?_⟩, fun _ => ⟨hint, ?_⟩⟩
          · have hx' := deep2 hx
            have hZne : Z.Nonempty := by
              by_contra h
              rw [Set.not_nonempty_iff_eq_empty] at h
              rw [h, convexHull_empty] at hx'
              exact hx'
            obtain ⟨y, hy⟩ := hZne
            obtain ⟨T, hT, _⟩ := deep1 y hy
            exact ⟨T, hT⟩
          · apply Set.Subset.antisymm
            · intro x hx
              have : x ∈ Z := by
                have h := hx
                unfold IntegralPolyhedron at hint
                rw [hint] at h
                exact extremePoints_convexHull_subset h
              exact deep1 x this
            · rintro x ⟨T, hT, rfl⟩
              refine ⟨easy T hT, ?_⟩
              intro y hy z hz hseg
              obtain ⟨a, b, ha, hb, hab, hxe⟩ := hseg
              have key : ∀ i, y i = packingVector D T i ∧ z i = packingVector D T i := by
                intro i
                have hi := congrFun hxe i
                simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
                have hy1 := hy.1 i; have hz1 := hz.1 i
                unfold packingVector at hi ⊢
                split_ifs at hi ⊢
                · constructor <;> nlinarith
                · constructor <;> nlinarith
              have e1 : y = packingVector D T := funext fun i => (key i).1
              have e2 : z = packingVector D T := funext fun i => (key i).2
              first | exact ⟨e1, e2⟩ | exact e1 | exact e1.trans e2.symm
