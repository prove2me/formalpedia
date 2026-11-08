-- Prove2me | solution 1 for ConsensusHalvingItems.Additive.reachable_step_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T23:52:44.952488+00:00
-- url     : https://prove2.me/submissions/2f2680b3-60a8-4489-9b45-1ff7a7f2d4fd

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_loopStep
import Definitions.Def_ConsensusHalvingItems_Additive_findSolution
import Definitions.Def_ConsensusHalvingItems_Additive_SolvesST
import Definitions.Def_ConsensusHalvingItems_Additive_inputSize
import Definitions.Def_ConsensusHalvingItems_Additive_Reachable
import Definitions.Def_ConsensusHalvingItems_Additive_bitSize

set_option autoImplicit false
set_option linter.all false

namespace ConsensusHalvingItems.Additive
namespace LSP

/-! ## Value of a ticked program (independent of the start counter) -/

theorem run_bind' {α β : Type} (p : StateM ℕ α) (f : α → StateM ℕ β) (t : ℕ) :
    (p >>= f).run t = (f (p.run t).1).run (p.run t).2 := rfl

def Val {α : Type} (p : StateM ℕ α) (a : α) : Prop := ∀ t, (p.run t).1 = a

theorem val_pure {α : Type} (a : α) : Val (pure a : StateM ℕ α) a := fun _ => rfl

theorem val_bind {α β : Type} {p : StateM ℕ α} {f : α → StateM ℕ β} {a : α} {b : β}
    (hp : Val p a) (hf : Val (f a) b) : Val (p >>= f) b := by
  intro t; rw [run_bind', hp t]; exact hf _

theorem val_tick (c : ℕ) : Val (tick c) () := fun _ => rfl
theorem val_qadd (a b : ℚ) : Val (qadd a b) (a + b) := fun _ => rfl
theorem val_qsub (a b : ℚ) : Val (qsub a b) (a - b) := fun _ => rfl
theorem val_qmul (a b : ℚ) : Val (qmul a b) (a * b) := fun _ => rfl
theorem val_qdiv (a b : ℚ) : Val (qdiv a b) (a / b) := fun _ => rfl
theorem val_qeq (a b : ℚ) : Val (qeq a b) (decide (a = b)) := fun _ => rfl
theorem val_qlt (a b : ℚ) : Val (qlt a b) (decide (a < b)) := fun _ => rfl
theorem val_uAt {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) (j : Fin m) :
    Val (uAt u i j) (u i j) := fun _ => rfl

theorem val_mapM {α β : Type} (f : α → StateM ℕ β) (g : α → β) (hf : ∀ a, Val (f a) (g a)) :
    ∀ l : List α, Val (l.mapM f) (l.map g)
  | [] => by simpa using val_pure ([] : List β)
  | a :: l => by
    rw [List.mapM_cons, List.map_cons]
    exact val_bind (hf a) (val_bind (val_mapM f g hf l) (val_pure _))

theorem val_foldlM {α β : Type} (f : β → α → StateM ℕ β) (g : β → α → β)
    (hf : ∀ b a, Val (f b a) (g b a)) :
    ∀ (l : List α) (b : β), Val (l.foldlM f b) (l.foldl g b)
  | [], b => by simpa using val_pure b
  | a :: l, b => by
    rw [List.foldlM_cons, List.foldl_cons]
    exact val_bind (hf b a) (val_foldlM f g hf l _)

theorem val_filterMapM {α β : Type} (f : α → StateM ℕ (Option β)) (g : α → Option β)
    (hf : ∀ a, Val (f a) (g a)) : ∀ l : List α, Val (l.filterMapM f) (l.filterMap g)
  | [] => by simpa using val_pure ([] : List β)
  | a :: l => by
    rw [List.filterMapM_cons, List.filterMap_cons]
    refine val_bind (hf a) ?_
    cases g a with
    | none => exact val_filterMapM f g hf l
    | some b => exact val_bind (val_filterMapM f g hf l) (val_pure _)

/-! ## Pure versions of the programs -/

def fpV (c : ℕ) : List (List ℚ) → Option (List ℚ × List (List ℚ))
  | [] => none
  | r :: rs =>
    if decide (r.getD c 0 = 0) = true then
      (match fpV c rs with
        | none => none
        | some (p, rest) => some (p, r :: rest))
    else some (r, rs)

def elimV (c : ℕ) (p r : List ℚ) : List ℚ :=
  (List.zip r p).map fun ab => ab.1 - r.getD c 0 * ab.2

def stepV {m : ℕ} (st : List (Fin m × List ℚ) × List (List ℚ)) (c : Fin m) :
    List (Fin m × List ℚ) × List (List ℚ) :=
  match fpV c.val st.2 with
  | none => st
  | some (p, rest) =>
    (st.1.map (fun qr => (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2)) ++
      [(c, p.map fun a => a / p.getD c.val 0)],
     rest.map (elimV c.val (p.map fun a => a / p.getD c.val 0)))

def dV {m : ℕ} (piv : List (Fin m × List ℚ)) (f : Fin m) (c : Fin m) : ℚ :=
  if c = f then 1 else
    match piv.find? (fun pr => pr.1 == c) with
    | some (_, r) => 0 - r.getD f.val 0
    | none => 0

def finalV {m : ℕ} (piv : List (Fin m × List ℚ)) : Option (Fin m → ℚ) :=
  match (List.finRange m).find? (fun c => !(piv.any fun pr => pr.1 == c)) with
  | none => none
  | some f => some fun c => ((List.finRange m).map (dV piv f)).getD c.val 0

def kernelDirV {m : ℕ} (rows : List (Fin m → ℚ)) : Option (Fin m → ℚ) :=
  finalV ((List.finRange m).foldl stepV
    ([], rows.map fun r => (List.finRange m).map r)).1

def urowV {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) : Fin m → ℚ :=
  fun j => ((List.finRange m).map fun j => u i j).getD j.val 0

def findSolutionV {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) :
    Option (Fin m → ℚ) :=
  match kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none) with
  | none => none
  | some d => some fun j => ((List.finRange m).map fun j => x j + d j).getD j.val 0

def gam {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) : ℚ :=
  if decide (x j < y j) = true then (1 - x j) / (y j - x j) else x j / (x j - y j)

def Fv {m : ℕ} (x y : Fin m → ℚ) (acc : Option (Fin m × ℚ)) (j : Fin m) :
    Option (Fin m × ℚ) :=
  if decide (y j = x j) = true then acc else
    match acc with
    | none => some (j, gam x y j)
    | some (_, g0) => if decide (gam x y j < g0) = true then some (j, gam x y j) else acc

def loopStepV {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) :
    Option (Finset (Fin m) × (Fin m → ℚ)) :=
  match findSolutionV u T x with
  | none => none
  | some y =>
    match (List.finRange m).foldl (Fv x y) none with
    | none => none
    | some (js, g) =>
      some (insert js T, fun j => ((List.finRange m).map fun j => (1 - g) * x j + g * y j).getD j.val 0)

/-! ## The programs compute their pure versions -/

theorem val_findPivot (c : ℕ) : ∀ l : List (List ℚ), Val (kernelDir.findPivot c l) (fpV c l)
  | [] => by rw [kernelDir.findPivot]; exact val_pure _
  | r :: rs => by
    rw [kernelDir.findPivot, fpV]
    refine val_bind (val_tick _) (val_bind (val_qeq _ _) ?_)
    cases decide (r.getD c 0 = 0)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact val_pure _
    · simp only [↓reduceIte]
      refine val_bind (val_findPivot c rs) ?_
      cases fpV c rs with
      | none => exact val_pure _
      | some pr => exact val_pure _

theorem val_elim (c : ℕ) (p r : List ℚ) : Val (kernelDir.elim c p r) (elimV c p r) := by
  unfold kernelDir.elim elimV
  exact val_mapM _ _ (fun ab => by
    rcases ab with ⟨a, b⟩
    exact val_bind (val_tick _) (val_bind (val_qmul _ _) (val_qsub _ _))) _

theorem val_kernelDir {m : ℕ} (rows : List (Fin m → ℚ)) :
    Val (kernelDir rows) (kernelDirV rows) := by
  unfold kernelDir kernelDirV
  refine val_bind (val_mapM _ (fun (r : Fin m → ℚ) => (List.finRange m).map r)
    (fun (r : Fin m → ℚ) => val_mapM _ (fun c => r c)
      (fun c => val_bind (val_tick _) (val_pure (r c))) _) _) ?_
  refine val_bind (val_foldlM _ stepV (fun st c => ?_) _ _) ?_
  · refine val_bind (val_tick _) ?_
    refine val_bind (val_findPivot _ _) ?_
    unfold stepV
    cases fpV c.val st.2 with
    | none => exact val_pure _
    | some pr =>
      obtain ⟨p, rest⟩ := pr
      dsimp only
      refine val_bind (val_mapM _ (fun a => a / p.getD c.val 0)
        (fun a => val_bind (val_tick _) (val_qdiv _ _)) _) ?_
      refine val_bind (val_mapM _
        (fun qr => (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2))
        (fun qr => ?_) _) ?_
      · rcases qr with ⟨q, r⟩
        exact val_bind (val_elim _ _ _) (val_pure _)
      · refine val_bind (val_mapM _ _ (fun r => val_elim _ _ _) _) ?_
        exact val_pure _
  · generalize (List.finRange m).foldl stepV
      ([], rows.map fun r => (List.finRange m).map r) = st
    dsimp only
    refine val_bind (val_tick _) ?_
    unfold finalV
    cases (List.finRange m).find? (fun c => !(st.1.any fun pr => pr.1 == c)) with
    | none => exact val_pure _
    | some f =>
      refine val_bind (val_mapM _ (dV st.1 f) (fun c => ?_) _) (val_pure _)
      refine val_bind (val_tick _) ?_
      unfold dV
      by_cases hc : c = f
      · rw [if_pos hc, if_pos hc]
        exact val_pure _
      · rw [if_neg hc, if_neg hc]
        cases st.1.find? (fun pr => pr.1 == c) with
        | none => exact val_pure _
        | some pr =>
          obtain ⟨q, r⟩ := pr
          exact val_qsub _ _

theorem val_findSolution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) : Val (findSolution u T x) (findSolutionV u T x) := by
  unfold findSolution findSolutionV
  refine val_bind (val_mapM _ (urowV u) (fun i => val_bind
    (val_mapM _ (fun j => u i j) (fun j => val_uAt u i j) _) (val_pure _)) _) ?_
  refine val_bind (val_filterMapM _
    (fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    (fun j => val_bind (val_tick _) (val_pure _)) _) ?_
  refine val_bind (val_kernelDir _) ?_
  cases kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none) with
  | none => exact val_pure _
  | some d =>
    exact val_bind (val_mapM _ (fun j => x j + d j) (fun j => val_qadd _ _) _) (val_pure _)

theorem val_loopStep {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) : Val (loopStep u T x) (loopStepV u T x) := by
  unfold loopStep loopStepV
  refine val_bind (val_findSolution u T x) ?_
  cases findSolutionV u T x with
  | none => exact val_pure _
  | some y =>
    dsimp only
    refine val_bind (val_foldlM _ (Fv x y) (fun acc j => ?_) _ _) ?_
    · refine val_bind (val_tick _) (val_bind (val_qeq _ _) ?_)
      unfold Fv
      cases decide (y j = x j)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine val_bind (val_qlt _ _) ?_
        have hm : ∀ g : ℚ, Val (match acc with
            | none => pure (some (j, g))
            | some (_, g0) => do
              let lt ← qlt g g0
              pure (if lt then some (j, g) else acc) : StateM ℕ (Option (Fin m × ℚ)))
            (match acc with
            | none => some (j, g)
            | some (_, g0) => if decide (g < g0) = true then some (j, g) else acc) := by
          intro g
          cases acc with
          | none => exact val_pure _
          | some pr =>
            obtain ⟨j0, g0⟩ := pr
            exact val_bind (val_qlt _ _) (val_pure _)
        unfold gam
        cases decide (x j < y j)
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact val_bind (val_qsub _ _) (val_bind (val_qdiv _ _) (hm _))
        · simp only [↓reduceIte]
          exact val_bind (val_qsub _ _) (val_bind (val_qsub _ _) (val_bind (val_qdiv _ _) (hm _)))
      · simp only [↓reduceIte]
        exact val_pure _
    · cases (List.finRange m).foldl (Fv x y) none with
      | none => exact val_pure _
      | some pr =>
        obtain ⟨js, g⟩ := pr
        dsimp only
        exact val_bind (val_mapM _ (fun j => (1 - g) * x j + g * y j)
          (fun j => val_bind (val_tick _) (val_bind (val_qsub _ _) (val_bind (val_qmul _ _)
            (val_bind (val_qmul _ _) (val_qadd _ _))))) _) (val_pure _)

/-! ## Soundness of the elimination -/

def dotL {m : ℕ} (r : List ℚ) (d : Fin m → ℚ) : ℚ := ∑ c : Fin m, r.getD c.val 0 * d c

theorem getD_map_finRange {m : ℕ} (f : Fin m → ℚ) (j : Fin m) :
    ((List.finRange m).map f).getD j.val 0 = f j := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem getD_map0 (f : ℚ → ℚ) (hf : f 0 = 0) :
    ∀ (l : List ℚ) (n : ℕ), (l.map f).getD n 0 = f (l.getD n 0)
  | [], n => by simp [hf]
  | a :: l, 0 => by simp
  | a :: l, n + 1 => by
    simp only [List.map_cons, List.getD_cons_succ]
    exact getD_map0 f hf l n

theorem getD_zipmap (s : ℚ) : ∀ (r p : List ℚ), r.length = p.length → ∀ n : ℕ,
    ((List.zip r p).map fun ab => ab.1 - s * ab.2).getD n 0 = r.getD n 0 - s * p.getD n 0
  | [], [], _, n => by simp
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: r, b :: p, _, 0 => by simp
  | a :: r, b :: p, h, n + 1 => by
    simp only [List.zip_cons_cons, List.map_cons, List.getD_cons_succ]
    exact getD_zipmap s r p (by simpa using h) n

theorem getD_elim (c : ℕ) (p r : List ℚ) (h : r.length = p.length) (n : ℕ) :
    (elimV c p r).getD n 0 = r.getD n 0 - r.getD c 0 * p.getD n 0 :=
  getD_zipmap _ r p h n

theorem length_elim (c : ℕ) (p r : List ℚ) :
    (elimV c p r).length = min r.length p.length := by
  simp [elimV]

theorem dot_elim {m : ℕ} (c : ℕ) (p r : List ℚ) (h : r.length = p.length) (d : Fin m → ℚ) :
    dotL (elimV c p r) d = dotL r d - r.getD c 0 * dotL p d := by
  unfold dotL
  simp only [getD_elim c p r h]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem dot_scale {m : ℕ} (p : List ℚ) (pc : ℚ) (d : Fin m → ℚ) :
    dotL (p.map fun a => a / pc) d = dotL p d / pc := by
  unfold dotL
  simp only [getD_map0 (fun a => a / pc) (zero_div pc)]
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem fpV_some (c : ℕ) : ∀ (l : List (List ℚ)) (p : List ℚ) (rest : List (List ℚ)),
    fpV c l = some (p, rest) →
      p ∈ l ∧ p.getD c 0 ≠ 0 ∧ (∀ r ∈ rest, r ∈ l) ∧ (∀ r ∈ l, r = p ∨ r ∈ rest)
  | [], p, rest, h => by simp [fpV] at h
  | r :: rs, p, rest, h => by
    rw [fpV] at h
    by_cases hz : r.getD c 0 = 0
    · rw [if_pos (by simpa using hz)] at h
      rcases hr : fpV c rs with _ | ⟨p1, rest1⟩
      · simp [hr] at h
      · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2, h3, h4⟩ := fpV_some c rs p1 rest1 hr
        refine ⟨List.mem_cons_of_mem _ h1, h2, ?_, ?_⟩
        · intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · simp
          · exact List.mem_cons_of_mem _ (h3 r' hr')
        · intro r' hr'
          rcases List.mem_cons.mp hr' with rfl | hr'
          · right; simp
          · rcases h4 r' hr' with h | h
            · left; exact h
            · right; exact List.mem_cons_of_mem _ h
    · rw [if_neg (by simpa using hz)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, hz, fun r' hr' => List.mem_cons_of_mem _ hr', fun r' hr' => List.mem_cons.mp hr'⟩

theorem fpV_none (c : ℕ) : ∀ l : List (List ℚ), fpV c l = none → ∀ r ∈ l, r.getD c 0 = 0
  | [], _, r, hr => by simp at hr
  | r :: rs, h, r', hr' => by
    rw [fpV] at h
    by_cases hz : r.getD c 0 = 0
    · rw [if_pos (by simpa using hz)] at h
      rcases hr : fpV c rs with _ | ⟨p1, rest1⟩
      · rcases List.mem_cons.mp hr' with rfl | hr'
        · exact hz
        · exact fpV_none c rs hr r' hr'
      · simp [hr] at h
    · rw [if_neg (by simpa using hz)] at h
      simp at h

def KInv {m : ℕ} (rows : List (Fin m → ℚ)) (S : Fin m → Prop)
    (st : List (Fin m × List ℚ) × List (List ℚ)) : Prop :=
  (∀ qr ∈ st.1, qr.2.length = m) ∧ (∀ r ∈ st.2, r.length = m) ∧
  (∀ qr ∈ st.1, qr.2.getD qr.1.val 0 = 1 ∧ S qr.1) ∧
  (∀ qr ∈ st.1, ∀ qr' ∈ st.1, qr'.1 ≠ qr.1 → qr.2.getD qr'.1.val 0 = 0) ∧
  (st.1.map Prod.fst).Nodup ∧
  (∀ r ∈ st.2, ∀ c : Fin m, S c → r.getD c.val 0 = 0) ∧
  (∀ d : Fin m → ℚ, (∀ qr ∈ st.1, dotL qr.2 d = 0) → (∀ r ∈ st.2, dotL r d = 0) →
    ∀ r ∈ rows, ∑ c, r c * d c = 0)

theorem kinv_step {m : ℕ} (rows : List (Fin m → ℚ)) (S : Fin m → Prop)
    (st : List (Fin m × List ℚ) × List (List ℚ)) (c : Fin m) (hc : ¬ S c)
    (h : KInv rows S st) : KInv rows (fun k => S k ∨ k = c) (stepV st c) := by
  obtain ⟨hL1, hL2, hP1, hP2, hN, hR, hS⟩ := h
  unfold stepV
  rcases hf : fpV c.val st.2 with _ | ⟨p, rest⟩
  · have h0 := fpV_none c.val st.2 hf
    refine ⟨hL1, hL2, fun qr hq => ⟨(hP1 qr hq).1, Or.inl (hP1 qr hq).2⟩, hP2, hN, ?_, hS⟩
    intro r hr k hk
    rcases hk with hk | rfl
    · exact hR r hr k hk
    · exact h0 r hr
  · obtain ⟨hp, hpc, hrest, hcov⟩ := fpV_some c.val st.2 p rest hf
    dsimp only
    have hpl : p.length = m := hL2 p hp
    have hp'l : (p.map fun a => a / p.getD c.val 0).length = m := by simp [hpl]
    have hp'g : ∀ j : ℕ, (p.map fun a => a / p.getD c.val 0).getD j 0 =
        p.getD j 0 / p.getD c.val 0 :=
      fun j => getD_map0 (fun a => a / p.getD c.val 0) (zero_div _) p j
    have hp'c : (p.map fun a => a / p.getD c.val 0).getD c.val 0 = 1 := by
      rw [hp'g]; exact div_self hpc
    have hp'S : ∀ k : Fin m, S k → (p.map fun a => a / p.getD c.val 0).getD k.val 0 = 0 :=
      fun k hk => by rw [hp'g, hR p hp k hk, zero_div]
    have hEl : ∀ r : List ℚ, r.length = m → ∀ j : ℕ,
        (elimV c.val (p.map fun a => a / p.getD c.val 0) r).getD j 0 =
          r.getD j 0 - r.getD c.val 0 * (p.map fun a => a / p.getD c.val 0).getD j 0 :=
      fun r hr j => getD_elim _ _ r (by rw [hr, hp'l]) j
    have hElL : ∀ r : List ℚ, r.length = m →
        (elimV c.val (p.map fun a => a / p.getD c.val 0) r).length = m :=
      fun r hr => by rw [length_elim, hr, hp'l, min_self]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro qr hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.mp hq
        exact hElL _ (hL1 qr0 hq0)
      · rw [List.mem_singleton] at hq; subst hq; exact hp'l
    · intro r hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      exact hElL _ (hL2 r0 (hrest r0 hr0))
    · intro qr hq
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.mp hq
        refine ⟨?_, Or.inl (hP1 qr0 hq0).2⟩
        dsimp only
        rw [hEl _ (hL1 qr0 hq0), hp'S _ (hP1 qr0 hq0).2, (hP1 qr0 hq0).1, mul_zero, sub_zero]
      · rw [List.mem_singleton] at hq; subst hq
        exact ⟨hp'c, Or.inr rfl⟩
    · intro qr hq qr' hq' hne
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.mp hq
        dsimp only at hne ⊢
        rw [hEl _ (hL1 qr0 hq0)]
        rcases List.mem_append.mp hq' with hq' | hq'
        · obtain ⟨qr1, hq1, rfl⟩ := List.mem_map.mp hq'
          dsimp only at hne ⊢
          rw [hP2 qr0 hq0 qr1 hq1 hne, hp'S _ (hP1 qr1 hq1).2, mul_zero, sub_zero]
        · rw [List.mem_singleton] at hq'; subst hq'
          dsimp only
          rw [hp'c, mul_one, sub_self]
      · rw [List.mem_singleton] at hq; subst hq
        rcases List.mem_append.mp hq' with hq' | hq'
        · obtain ⟨qr1, hq1, rfl⟩ := List.mem_map.mp hq'
          exact hp'S _ (hP1 qr1 hq1).2
        · rw [List.mem_singleton] at hq'; subst hq'
          exact absurd rfl hne
    · rw [List.map_append, List.map_map, List.nodup_append_comm]
      have e : (Prod.fst ∘ fun qr : Fin m × List ℚ =>
          (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2)) = Prod.fst := rfl
      rw [e]
      simp only [List.map_cons, List.map_nil, List.singleton_append, List.nodup_cons]
      refine ⟨fun hm => ?_, hN⟩
      obtain ⟨qr, hq, hqc⟩ := List.mem_map.mp hm
      exact hc (hqc ▸ (hP1 qr hq).2)
    · intro r hr k hk
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
      have hr0' := hrest r0 hr0
      rw [hEl _ (hL2 r0 hr0')]
      rcases hk with hk | rfl
      · rw [hR r0 hr0' k hk, hp'S k hk, mul_zero, sub_zero]
      · rw [hp'c, mul_one, sub_self]
    · intro d hpiv hrst
      have hdp' : dotL (p.map fun a => a / p.getD c.val 0) d = 0 :=
        hpiv (c, p.map fun a => a / p.getD c.val 0) (by simp)
      have hdp : dotL p d = 0 := by
        rw [dot_scale] at hdp'
        rcases div_eq_zero_iff.mp hdp' with h | h
        · exact h
        · exact absurd h hpc
      have hE : ∀ r : List ℚ, r.length = m →
          dotL (elimV c.val (p.map fun a => a / p.getD c.val 0) r) d = 0 → dotL r d = 0 := by
        intro r hr h0
        rw [dot_elim _ _ _ (by rw [hr, hp'l]), hdp', mul_zero, sub_zero] at h0
        exact h0
      refine hS d (fun qr hq => ?_) (fun r hr => ?_)
      · exact hE _ (hL1 qr hq) (hpiv _ (List.mem_append_left _ (List.mem_map_of_mem hq)))
      · rcases hcov r hr with rfl | hr'
        · exact hdp
        · exact hE _ (hL2 r hr) (hrst _ (List.mem_map_of_mem hr'))

theorem kinv_foldl {m : ℕ} (rows : List (Fin m → ℚ)) :
    ∀ (l : List (Fin m)) (S : Fin m → Prop) (st : List (Fin m × List ℚ) × List (List ℚ)),
      l.Nodup → (∀ c ∈ l, ¬ S c) → KInv rows S st →
      KInv rows (fun k => S k ∨ k ∈ l) (l.foldl stepV st)
  | [], S, st, _, _, h => by
    have e : (fun k => S k ∨ k ∈ ([] : List (Fin m))) = S := by funext k; simp
    rw [List.foldl_nil, e]; exact h
  | c :: l, S, st, hnd, hdis, h => by
    rw [List.foldl_cons]
    have hnd' := List.nodup_cons.mp hnd
    have h1 := kinv_step rows S st c (hdis c (by simp)) h
    have h2 := kinv_foldl rows l (fun k => S k ∨ k = c) (stepV st c) hnd'.2
      (fun k hk hSk => hSk.elim (fun hs => hdis k (List.mem_cons_of_mem c hk) hs)
        (fun he => hnd'.1 (he ▸ hk))) h1
    have e : (fun k => (S k ∨ k = c) ∨ k ∈ l) = (fun k => S k ∨ k ∈ c :: l) := by
      funext k; apply propext; simp only [List.mem_cons]; tauto
    rw [← e]; exact h2

theorem kernel_sound {m : ℕ} (rows : List (Fin m → ℚ)) (d : Fin m → ℚ)
    (h : kernelDirV rows = some d) : ∀ r ∈ rows, ∑ c, r c * d c = 0 := by
  unfold kernelDirV at h
  have h0 : KInv rows (fun _ => False) ([], rows.map fun r => (List.finRange m).map r) := by
    refine ⟨by simp, ?_, by simp, by simp, by simp, fun _ _ _ hc => hc.elim, ?_⟩
    · intro r hr
      obtain ⟨r0, _, rfl⟩ := List.mem_map.mp hr
      simp
    · intro d _ hd r hr
      have := hd _ (List.mem_map.2 ⟨r, hr, rfl⟩)
      unfold dotL at this
      simpa only [getD_map_finRange] using this
  have hF := kinv_foldl rows (List.finRange m) _ _ (List.nodup_finRange m) (fun c _ h => h) h0
  generalize (List.finRange m).foldl stepV ([], rows.map fun r => (List.finRange m).map r) = st
    at h hF
  obtain ⟨_, _, hP1, hP2, hN, hR, hS⟩ := hF
  unfold finalV at h
  rcases hf : (List.finRange m).find? (fun c => !(st.1.any fun pr => pr.1 == c)) with _ | f
  · simp [hf] at h
  simp only [hf, Option.some.injEq] at h
  subst h
  have hfree : ∀ qr ∈ st.1, qr.1 ≠ f := by
    intro qr hq hqf
    have h1 := List.find?_some hf
    have h2 : (st.1.any fun pr => pr.1 == f) = true := List.any_eq_true.2 ⟨qr, hq, by simp [hqf]⟩
    simp [h2] at h1
  apply hS
  · intro qr hq
    unfold dotL
    simp only [getD_map_finRange]
    have hterm : ∀ c : Fin m, qr.2.getD c.val 0 * dV st.1 f c =
        (if c = qr.1 then -(qr.2.getD f.val 0) else 0) +
          (if c = f then qr.2.getD f.val 0 else 0) := by
      intro c
      unfold dV
      by_cases hcf : c = f
      · subst hcf
        have hne : c ≠ qr.1 := fun e => hfree qr hq e.symm
        rw [if_pos rfl, if_pos rfl, if_neg hne]
        ring
      · rw [if_neg hcf, if_neg hcf, add_zero]
        rcases hq2 : st.1.find? (fun pr => pr.1 == c) with _ | ⟨c', r'⟩
        · have hnone := List.find?_eq_none.mp hq2
          have hcq : c ≠ qr.1 := by
            intro e
            exact hnone qr hq (by simp [e])
          simp only [hq2, if_neg hcq]
          ring
        · have hm := List.mem_of_find?_eq_some hq2
          have hp := List.find?_some hq2
          have hc' : c' = c := by simpa using hp
          simp only [hq2]
          by_cases hcq : c = qr.1
          · rw [if_pos hcq]
            have e : (c', r') = qr :=
              List.inj_on_of_nodup_map hN hm hq (by simp [hc', hcq])
            subst e
            have h1 := (hP1 _ hq).1
            dsimp only at h1
            rw [← hc', h1]
            ring
          · rw [if_neg hcq]
            have := hP2 qr hq (c', r') hm (by simpa [hc'] using hcq)
            simp only [hc'] at this
            rw [this]
            ring
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp
  · intro r hr
    unfold dotL
    simp only [getD_map_finRange]
    apply Finset.sum_eq_zero
    intro c _
    rw [hR r hr c (Or.inr (List.mem_finRange c)), zero_mul]

theorem findSolution_sound {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x y : Fin m → ℚ) (h : findSolutionV u T x = some y) :
    ∃ d : Fin m → ℚ, (∀ i, ∑ j, u i j * d j = 0) ∧ ∀ j, y j = x j + d j := by
  unfold findSolutionV at h
  rcases hk : kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    with _ | d
  · simp [hk] at h
  simp only [hk, Option.some.injEq] at h
  subst h
  refine ⟨d, fun i => ?_, fun j => getD_map_finRange _ j⟩
  have := kernel_sound _ d hk (urowV u i)
    (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  simpa only [urowV, getD_map_finRange] using this

/-! ## The ratio scan -/

def Inv2 {m : ℕ} (x y : Fin m → ℚ) (S : Fin m → Prop) (acc : Option (Fin m × ℚ)) : Prop :=
  (∀ js g, acc = some (js, g) →
    y js ≠ x js ∧ g = gam x y js ∧ ∀ j, S j → y j ≠ x j → g ≤ gam x y j) ∧
  (acc = none → ∀ j, S j → y j = x j)

theorem inv2_step {m : ℕ} (x y : Fin m → ℚ) (S : Fin m → Prop) (acc : Option (Fin m × ℚ))
    (j : Fin m) (h : Inv2 x y S acc) : Inv2 x y (fun k => S k ∨ k = j) (Fv x y acc j) := by
  obtain ⟨h1, h2⟩ := h
  unfold Fv
  by_cases hj : y j = x j
  · rw [if_pos (by simpa using hj)]
    refine ⟨fun js g hacc => ?_, fun hacc k hk => ?_⟩
    · obtain ⟨a, b, c⟩ := h1 js g hacc
      refine ⟨a, b, fun k hk hne => ?_⟩
      rcases hk with hk | rfl
      · exact c k hk hne
      · exact absurd hj hne
    · rcases hk with hk | rfl
      · exact h2 hacc k hk
      · exact hj
  · rw [if_neg (by simpa using hj)]
    cases acc with
    | none =>
      dsimp only
      refine ⟨fun js g hacc => ?_, fun hacc => by cases hacc⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hacc
      obtain ⟨rfl, rfl⟩ := hacc
      refine ⟨hj, rfl, fun k hk hne => ?_⟩
      rcases hk with hk | rfl
      · exact absurd (h2 rfl k hk) hne
      · exact le_refl _
    | some pr =>
      obtain ⟨j0, g0⟩ := pr
      obtain ⟨a0, b0, c0⟩ := h1 j0 g0 rfl
      dsimp only
      by_cases hlt : gam x y j < g0
      · rw [if_pos (by simpa using hlt)]
        refine ⟨fun js g hacc => ?_, fun hacc => by cases hacc⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hacc
        obtain ⟨rfl, rfl⟩ := hacc
        refine ⟨hj, rfl, fun k hk hne => ?_⟩
        rcases hk with hk | rfl
        · exact le_of_lt (lt_of_lt_of_le hlt (c0 k hk hne))
        · exact le_refl _
      · rw [if_neg (by simpa using hlt)]
        refine ⟨fun js g hacc => ?_, fun hacc => by cases hacc⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hacc
        obtain ⟨rfl, rfl⟩ := hacc
        refine ⟨a0, b0, fun k hk hne => ?_⟩
        rcases hk with hk | rfl
        · exact c0 k hk hne
        · exact not_lt.1 hlt

theorem inv2_foldl {m : ℕ} (x y : Fin m → ℚ) :
    ∀ (l : List (Fin m)) (S : Fin m → Prop) (acc : Option (Fin m × ℚ)), Inv2 x y S acc →
      Inv2 x y (fun k => S k ∨ k ∈ l) (l.foldl (Fv x y) acc)
  | [], S, acc, h => by
    have e : (fun k => S k ∨ k ∈ ([] : List (Fin m))) = S := by funext k; simp
    rw [List.foldl_nil, e]; exact h
  | j :: l, S, acc, h => by
    rw [List.foldl_cons]
    have h2 := inv2_foldl x y l _ _ (inv2_step x y S acc j h)
    have e : (fun k => (S k ∨ k = j) ∨ k ∈ l) = (fun k => S k ∨ k ∈ j :: l) := by
      funext k; apply propext; simp only [List.mem_cons]; tauto
    rw [← e]; exact h2

theorem fold_spec {m : ℕ} (x y : Fin m → ℚ) (js : Fin m) (g : ℚ)
    (h : (List.finRange m).foldl (Fv x y) none = some (js, g)) :
    y js ≠ x js ∧ g = gam x y js ∧ ∀ j, y j ≠ x j → g ≤ gam x y j := by
  have h0 : Inv2 x y (fun _ => False) none := ⟨fun js g h => (by cases h), fun _ j hj => hj.elim⟩
  have := (inv2_foldl x y (List.finRange m) _ none h0).1 js g h
  exact ⟨this.1, this.2.1, fun j hj => this.2.2 j (Or.inr (List.mem_finRange j)) hj⟩

theorem gam_up {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) (h : x j < y j) :
    gam x y j * (y j - x j) = 1 - x j := by
  unfold gam
  rw [if_pos (by simpa using h)]
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 h))

theorem gam_down {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) (h : y j < x j) :
    gam x y j * (x j - y j) = x j := by
  unfold gam
  rw [if_neg (by simpa using not_lt.2 h.le)]
  exact div_mul_cancel₀ _ (ne_of_gt (sub_pos.2 h))

theorem gam_nonneg {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) (hf : 0 ≤ x j ∧ x j ≤ 1)
    (hne : y j ≠ x j) : 0 ≤ gam x y j := by
  unfold gam
  by_cases h : x j < y j
  · rw [if_pos (by simpa using h)]
    exact div_nonneg (sub_nonneg.2 hf.2) (sub_pos.2 h).le
  · rw [if_neg (by simpa using h)]
    have h' : y j < x j := lt_of_le_of_ne (not_lt.1 h) hne
    exact div_nonneg hf.1 (sub_pos.2 h').le


theorem findSolution_fix {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x y : Fin m → ℚ) (h : findSolutionV u T x = some y) : ∀ j ∈ T, y j = x j := by
  unfold findSolutionV at h
  rcases hk : kernelDirV ((List.finRange n).map (urowV u) ++
      (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    with _ | d
  · simp [hk] at h
  simp only [hk, Option.some.injEq] at h
  subst h
  intro j hj
  have := kernel_sound _ d hk (Pi.single j (1 : ℚ))
    (List.mem_append_right _ (List.mem_filterMap.2 ⟨j, List.mem_finRange j, by simp [hj]⟩))
  simp [Pi.single_apply] at this
  show ((List.finRange m).map fun j => x j + d j).getD j.val 0 = x j
  rw [getD_map_finRange, this, add_zero]

/-! ## findSolution_spec (ec59e0f2) additions -/

theorem finalV_some {m : ℕ} (piv : List (Fin m × List ℚ)) (d : Fin m → ℚ)
    (h : finalV piv = some d) : ∃ f : Fin m, d f = 1 ∧ ¬ (piv.any fun pr => pr.1 == f) = true := by
  unfold finalV at h
  rcases hf : (List.finRange m).find? (fun c => !(piv.any fun pr => pr.1 == c)) with _ | f
  · simp [hf] at h
  simp only [hf, Option.some.injEq] at h
  subst h
  refine ⟨f, ?_, ?_⟩
  · show ((List.finRange m).map (dV piv f)).getD f.val 0 = 1
    rw [getD_map_finRange]; unfold dV; simp
  · have h1 := List.find?_some hf
    revert h1; simp
    intro H b hb; exact H f b hb rfl

def sysRows {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) : List (Fin m → ℚ) :=
  (List.finRange n).map (urowV u) ++
    (List.finRange m).filterMap fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none


def toF {m : ℕ} (r : List ℚ) : Fin m → ℚ := fun c => r.getD c.val 0

theorem toF_elim {m : ℕ} (c : ℕ) (p r : List ℚ) (h : r.length = p.length) :
    (toF (elimV c p r) : Fin m → ℚ) = toF r - r.getD c 0 • toF p := by
  funext j
  simp only [toF, getD_elim c p r h, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

theorem toF_scale {m : ℕ} (p : List ℚ) (pc : ℚ) :
    (toF (p.map fun a => a / pc) : Fin m → ℚ) = pc⁻¹ • toF p := by
  funext j
  simp only [toF, getD_map0 (fun a => a / pc) (zero_div pc), Pi.smul_apply, smul_eq_mul]
  ring

def PInv {m : ℕ} (rows : List (Fin m → ℚ)) (st : List (Fin m × List ℚ) × List (List ℚ)) : Prop :=
  (∀ qr ∈ st.1, qr.2.length = m) ∧ (∀ r ∈ st.2, r.length = m) ∧
  ∃ O : List (Fin m → ℚ), O.length = st.1.length ∧ (∀ o ∈ O, o ∈ rows) ∧
    (∀ qr ∈ st.1, (toF qr.2 : Fin m → ℚ) ∈ Submodule.span ℚ {o | o ∈ O}) ∧
    (∀ r ∈ st.2, ∃ a ∈ rows, (toF r : Fin m → ℚ) - a ∈ Submodule.span ℚ {o | o ∈ O})

theorem pinv_step {m : ℕ} (rows : List (Fin m → ℚ))
    (st : List (Fin m × List ℚ) × List (List ℚ)) (c : Fin m)
    (h : PInv rows st) : PInv rows (stepV st c) := by
  obtain ⟨hL1, hL2, O, hOl, hOr, hP, hR⟩ := h
  unfold stepV
  rcases hf : fpV c.val st.2 with _ | ⟨p, rest⟩
  · exact ⟨hL1, hL2, O, hOl, hOr, hP, hR⟩
  · obtain ⟨hp, -, hrest, -⟩ := fpV_some c.val st.2 p rest hf
    dsimp only
    have hpl : p.length = m := hL2 p hp
    have hp'l : (p.map fun a => a / p.getD c.val 0).length = m := by simp [hpl]
    obtain ⟨a, ha, hpa⟩ := hR p hp
    have hsub : Submodule.span ℚ {o | o ∈ O} ≤ Submodule.span ℚ {o | o ∈ O ++ [a]} :=
      Submodule.span_mono fun o ho => List.mem_append_left _ ho
    have haS : a ∈ Submodule.span ℚ {o | o ∈ O ++ [a]} :=
      Submodule.subset_span (List.mem_append_right _ (List.mem_singleton_self a))
    have hpS : (toF p : Fin m → ℚ) ∈ Submodule.span ℚ {o | o ∈ O ++ [a]} := by
      have := Submodule.add_mem _ (hsub hpa) haS
      rwa [sub_add_cancel] at this
    have hp'S : (toF (p.map fun a => a / p.getD c.val 0) : Fin m → ℚ) ∈
        Submodule.span ℚ {o | o ∈ O ++ [a]} := by
      rw [toF_scale]; exact Submodule.smul_mem _ _ hpS
    refine ⟨?_, ?_, O ++ [a], ?_, ?_, ?_, ?_⟩
    · intro qr hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.1 hq
        simp only [length_elim, hL1 qr0 hq0, hp'l, min_self]
      · simp only [List.mem_singleton] at hq; subst hq; exact hp'l
    · intro r hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
      simp only [length_elim, hL2 r0 (hrest r0 hr0), hp'l, min_self]
    · simp [hOl]
    · intro o ho
      rcases List.mem_append.1 ho with ho | ho
      · exact hOr o ho
      · simp only [List.mem_singleton] at ho; subst ho; exact ha
    · intro qr hq
      rcases List.mem_append.1 hq with hq | hq
      · obtain ⟨qr0, hq0, rfl⟩ := List.mem_map.1 hq
        dsimp only
        rw [toF_elim _ _ _ (by rw [hL1 qr0 hq0, hp'l])]
        exact Submodule.sub_mem _ (hsub (hP qr0 hq0)) (Submodule.smul_mem _ _ hp'S)
      · simp only [List.mem_singleton] at hq; subst hq; exact hp'S
    · intro r hr
      obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
      obtain ⟨b, hb, hrb⟩ := hR r0 (hrest r0 hr0)
      refine ⟨b, hb, ?_⟩
      rw [toF_elim _ _ _ (by rw [hL2 r0 (hrest r0 hr0), hp'l])]
      have e : (toF r0 : Fin m → ℚ) - r0.getD c.val 0 • toF (p.map fun a => a / p.getD c.val 0) - b
          = (toF r0 - b) - r0.getD c.val 0 • toF (p.map fun a => a / p.getD c.val 0) := by abel
      rw [e]
      exact Submodule.sub_mem _ (hsub hrb) (Submodule.smul_mem _ _ hp'S)

theorem pinv_foldl {m : ℕ} (rows : List (Fin m → ℚ)) :
    ∀ (l : List (Fin m)) (st : List (Fin m × List ℚ) × List (List ℚ)),
      PInv rows st → PInv rows (l.foldl stepV st)
  | [], st, h => h
  | c :: l, st, h => by
    rw [List.foldl_cons]; exact pinv_foldl rows l _ (pinv_step rows st c h)

theorem pinv_init {m : ℕ} (rows : List (Fin m → ℚ)) :
    PInv rows ([], rows.map fun r => (List.finRange m).map r) := by
  refine ⟨by simp, ?_, [], rfl, by simp, by simp, ?_⟩
  · intro r hr
    obtain ⟨r0, _, rfl⟩ := List.mem_map.mp hr
    simp
  · intro r hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    refine ⟨r0, hr0, ?_⟩
    have : (toF ((List.finRange m).map r0) : Fin m → ℚ) = r0 := by
      funext j; exact getD_map_finRange r0 j
    rw [this, sub_self]; exact Submodule.zero_mem _


/-! ## Step C (core): Cramer representation of the stage entries -/

theorem cramer_rep {s m : ℕ} (A : Fin s → Fin m → ℚ) (J : Fin s → Fin m) (P : Fin s → Fin m → ℚ)
    (hP : ∀ k, P k ∈ Submodule.span ℚ (Set.range A))
    (hJ : ∀ k l, P k (J l) = if k = l then 1 else 0) :
    (Matrix.of fun l l' => A l (J l')).det ≠ 0 ∧
    ∀ k c, P k c = ((Matrix.of fun l l' => A l (J l')).updateCol k (fun l => A l c)).det /
      (Matrix.of fun l l' => A l (J l')).det := by
  have hW : ∀ k, ∃ w : Fin s → ℚ, ∑ l, w l • A l = P k :=
    fun k => (Submodule.mem_span_range_iff_exists_fun ℚ).1 (hP k)
  choose W hW using hW
  have hPc : ∀ k c, P k c = ∑ l, W k l * A l c := by
    intro k c; rw [← hW k]; simp [Finset.sum_apply]
  have hWA : Matrix.of W * (Matrix.of fun l l' => A l (J l')) = 1 := by
    ext k l'
    rw [Matrix.mul_apply, Matrix.one_apply, ← hJ k l', hPc]
    simp
  have hdet : (Matrix.of fun l l' => A l (J l')).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hWA
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  refine ⟨hdet, fun k c => ?_⟩
  have hinv : (Matrix.of fun l l' => A l (J l'))⁻¹ = Matrix.of W := Matrix.inv_eq_left_inv hWA
  have e1 : P k c = (Matrix.mulVec (Matrix.of fun l l' => A l (J l'))⁻¹ fun l => A l c) k := by
    rw [hinv, hPc]; simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.inv_def, Matrix.smul_mulVec, ← Matrix.cramer_eq_adjugate_mulVec,
    Pi.smul_apply, Matrix.cramer_apply, Ring.inverse_eq_inv', smul_eq_mul, div_eq_inv_mul]

theorem rest_rep {s m : ℕ} (A : Fin s → Fin m → ℚ) (J : Fin s → Fin m) (P : Fin s → Fin m → ℚ)
    (hP : ∀ k, P k ∈ Submodule.span ℚ (Set.range A))
    (hJ : ∀ k l, P k (J l) = if k = l then 1 else 0) (a r : Fin m → ℚ)
    (hr : r - a ∈ Submodule.span ℚ (Set.range A)) (hrJ : ∀ l, r (J l) = 0) :
    ∀ c, r c = a c - ∑ k, a (J k) * P k c := by
  intro c
  obtain ⟨hdet, -⟩ := cramer_rep A J P hP hJ
  have hz : r - a + ∑ k, a (J k) • P k ∈ Submodule.span ℚ (Set.range A) :=
    Submodule.add_mem _ hr (Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hP k))
  obtain ⟨ν, hν⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hz
  have hzJ : ∀ l', (r - a + ∑ k, a (J k) • P k) (J l') = 0 := by
    intro l'
    simp [Finset.sum_apply, hJ, hrJ]
  have hvm : Matrix.vecMul ν (Matrix.of fun l l' => A l (J l')) = 0 := by
    funext l'
    rw [Pi.zero_apply, ← hzJ l', ← hν]
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
  have hν0 : ν = 0 := by
    have hu : IsUnit (Matrix.of fun l l' => A l (J l')).det := isUnit_iff_ne_zero.2 hdet
    calc ν = Matrix.vecMul (Matrix.vecMul ν (Matrix.of fun l l' => A l (J l')))
          (Matrix.of fun l l' => A l (J l'))⁻¹ := by
            rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one]
      _ = 0 := by rw [hvm, Matrix.zero_vecMul]
  have hz0 : r - a + ∑ k, a (J k) • P k = 0 := by rw [← hν, hν0]; simp
  have := congrFun hz0 c
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply] at this
  linarith


theorem bitSize_intdiv_le (N Q : ℤ) (hQ : Q ≠ 0) :
    bitSize ((N : ℚ) / Q) ≤ Nat.size N.natAbs + Nat.size Q.natAbs + 1 := by
  unfold bitSize
  have h1 : ((N : ℚ) / Q).num.natAbs ≤ N.natAbs := by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · have d := Rat.num_dvd N hQ
      rw [Rat.divInt_eq_div] at d
      exact Nat.le_of_dvd (Int.natAbs_pos.2 hN) (Int.natAbs_dvd_natAbs.2 d)
  have h2 : ((N : ℚ) / Q).den ≤ Q.natAbs := by
    have d := Rat.den_dvd N Q
    rw [Rat.divInt_eq_div] at d
    exact Nat.le_of_dvd (Int.natAbs_pos.2 hQ) (by simpa using Int.natAbs_dvd_natAbs.2 d)
  have := Nat.size_le_size h1
  have := Nat.size_le_size h2
  omega



/-! ## Step C assembly: every Gauss-Jordan stage entry has bounded bit size -/

def Dn {m : ℕ} (rows : List (Fin m → ℚ)) : ℕ := (rows.map fun r => ∏ c, (r c).den).prod

def Kb {m : ℕ} (rows : List (Fin m → ℚ)) : ℕ := (rows.map fun r => ∑ c, bitSize (r c)).sum

def Bst (m K : ℕ) : ℕ :=
  2 * Nat.size ((m + 1) * 2 ^ (2 * K) * (m.factorial * (2 ^ (2 * K)) ^ m)) + 1

theorem dn_pos {m : ℕ} (rows : List (Fin m → ℚ)) : 0 < Dn rows := by
  unfold Dn
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (Finset.prod_pos fun c _ => (r c).den_pos) ih

theorem dn_le {m : ℕ} (rows : List (Fin m → ℚ)) : Dn rows ≤ 2 ^ Kb rows := by
  unfold Dn Kb
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.prod_cons, List.sum_cons, pow_add]
    refine Nat.mul_le_mul ?_ ih
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun c _ => ?_
    have h1 : (r c).den < 2 ^ Nat.size (r c).den := Nat.lt_size_self _
    have h2 : 2 ^ Nat.size (r c).den ≤ 2 ^ bitSize (r c) :=
      Nat.pow_le_pow_right (by norm_num) (by unfold bitSize; omega)
    omega

theorem ent_le {m : ℕ} {rows : List (Fin m → ℚ)} {r : Fin m → ℚ} (hr : r ∈ rows) (c : Fin m) :
    bitSize (r c) ≤ Kb rows := by
  unfold Kb
  have h1 : bitSize (r c) ≤ ∑ c, bitSize (r c) :=
    Finset.single_le_sum (f := fun c => bitSize (r c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  have h2 : ∑ c, bitSize (r c) ≤ (rows.map fun r => ∑ c, bitSize (r c)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨r, hr, rfl⟩)
  omega

theorem den_dvd_dn {m : ℕ} {rows : List (Fin m → ℚ)} {r : Fin m → ℚ} (hr : r ∈ rows) (c : Fin m) :
    (r c).den ∣ Dn rows :=
  (Finset.dvd_prod_of_mem (fun c => (r c).den) (Finset.mem_univ c)).trans
    (List.dvd_prod (List.mem_map.2 ⟨r, hr, rfl⟩))

theorem scaled_int {m : ℕ} {rows : List (Fin m → ℚ)} {r : Fin m → ℚ} (hr : r ∈ rows) (c : Fin m) :
    ∃ z : ℤ, (Dn rows : ℚ) * r c = z ∧ |z| ≤ 2 ^ (2 * Kb rows) := by
  obtain ⟨k, hk⟩ := den_dvd_dn hr c
  refine ⟨(k : ℤ) * (r c).num, ?_, ?_⟩
  · rw [hk]
    have := Rat.mul_den_eq_num (r c)
    push_cast
    calc ((r c).den : ℚ) * k * r c = k * (r c * (r c).den) := by ring
      _ = _ := by rw [this]
  · have hD := dn_le rows
    have hn : (r c).num.natAbs < 2 ^ Kb rows := by
      have h1 := Nat.lt_size_self (r c).num.natAbs
      have h2 : Nat.size (r c).num.natAbs ≤ Kb rows := by
        have := ent_le hr c; unfold bitSize at this; omega
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by norm_num) h2)
    have hk' : k ≤ Dn rows := Nat.le_of_dvd (dn_pos rows) ⟨(r c).den, by rw [hk]; ring⟩
    rw [Int.abs_eq_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
    have : k * (r c).num.natAbs ≤ 2 ^ (2 * Kb rows) := by
      rw [two_mul, pow_add]; exact Nat.mul_le_mul (hk'.trans hD) hn.le
    exact_mod_cast this

theorem det_int_bound {s : ℕ} (X : Matrix (Fin s) (Fin s) ℚ) (Dq : ℚ) (W : ℤ)
    (hX : ∀ i j, ∃ z : ℤ, Dq * X i j = z ∧ |z| ≤ W) :
    ∃ z : ℤ, Dq ^ s * X.det = z ∧ |z| ≤ s.factorial * W ^ s := by
  choose Z hZ hZb using hX
  refine ⟨(Matrix.of Z).det, ?_, ?_⟩
  · have h1 : Dq • X = (Matrix.of Z).map (Int.castRingHom ℚ) := by
      ext i j; simp [hZ]
    have h3 := Matrix.det_smul X Dq
    rw [Fintype.card_fin] at h3
    rw [← h3, h1]
    have h2 := RingHom.map_det (Int.castRingHom ℚ) (Matrix.of Z)
    simp only [eq_intCast] at h2
    exact h2.symm
  · have := Matrix.det_le (A := Matrix.of Z) (abv := AbsoluteValue.abs) (x := W)
      (fun i j => by simpa using hZb i j)
    simpa [Fintype.card_fin, nsmul_eq_mul] using this

theorem bitSize_frac_le (N Q : ℤ) (hQ : Q ≠ 0) (Bn : ℕ) (hN : |N| ≤ Bn) (hQb : |Q| ≤ Bn) :
    bitSize ((N : ℚ) / Q) ≤ 2 * Nat.size Bn + 1 := by
  have h := bitSize_intdiv_le N Q hQ
  have h1 : N.natAbs ≤ Bn := by rw [Int.abs_eq_natAbs] at hN; exact_mod_cast hN
  have h2 : Q.natAbs ≤ Bn := by rw [Int.abs_eq_natAbs] at hQb; exact_mod_cast hQb
  have := Nat.size_le_size h1
  have := Nat.size_le_size h2
  omega

theorem stage_bound {m : ℕ} (rows : List (Fin m → ℚ)) (S : Fin m → Prop)
    (st : List (Fin m × List ℚ) × List (List ℚ)) (hK : KInv rows S st) (hPI : PInv rows st) :
    (∀ qr ∈ st.1, ∀ c : Fin m, bitSize (toF qr.2 c) ≤ Bst m (Kb rows)) ∧
    (∀ r ∈ st.2, ∀ c : Fin m, bitSize (toF r c) ≤ Bst m (Kb rows)) := by
  obtain ⟨_, _, hP1, hP2, hN, hR, _⟩ := hK
  obtain ⟨_, _, O, hOl, hOr, hOs, hOrest⟩ := hPI
  have hsm : st.1.length ≤ m := by
    have := hN.length_le_card; simpa using this
  set s := st.1.length with hs
  set W : ℤ := 2 ^ (2 * Kb rows) with hW
  set Dz : ℤ := (Dn rows : ℤ) with hDz
  let A : Fin s → Fin m → ℚ := fun k => O.get (Fin.cast hOl.symm k)
  let J : Fin s → Fin m := fun k => (st.1.get k).1
  let P : Fin s → Fin m → ℚ := fun k => toF (st.1.get k).2
  have hspan : Submodule.span ℚ {o | o ∈ O} = Submodule.span ℚ (Set.range A) := by
    congr 1; ext o
    simp only [Set.mem_ofPred_eq, Set.mem_range, A]
    rw [List.mem_iff_get]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨Fin.cast hOl k, rfl⟩
    · rintro ⟨k, rfl⟩; exact ⟨_, rfl⟩
  have hArows : ∀ k, A k ∈ rows := fun k => hOr _ (List.get_mem _ _)
  have hP : ∀ k, P k ∈ Submodule.span ℚ (Set.range A) := fun k => hspan ▸ hOs _ (List.get_mem _ _)
  have hJ : ∀ k l, P k (J l) = if k = l then 1 else 0 := by
    intro k l
    split_ifs with h
    · subst h; exact (hP1 _ (List.get_mem _ _)).1
    · refine hP2 _ (List.get_mem _ _) _ (List.get_mem _ _) ?_
      intro heq; apply h
      have h2 := (hN.getElem_inj_iff (i := l.val) (j := k.val) (hi := by rw [List.length_map]; exact l.isLt)
        (hj := by rw [List.length_map]; exact k.isLt)).1 (by simpa [J] using heq)
      exact Fin.ext h2.symm
  obtain ⟨hdet, hrep⟩ := cramer_rep A J P hP hJ
  set M0 : Matrix (Fin s) (Fin s) ℚ := Matrix.of fun l l' => A l (J l') with hM0
  have hAint : ∀ l j, ∃ z : ℤ, (Dn rows : ℚ) * A l j = z ∧ |z| ≤ W :=
    fun l j => scaled_int (hArows l) j
  have hM0i : ∀ i j, ∃ z : ℤ, (Dn rows : ℚ) * M0 i j = z ∧ |z| ≤ W :=
    fun i j => hAint i (J j)
  have hU : ∀ k c i j, ∃ z : ℤ, (Dn rows : ℚ) * (M0.updateCol k (fun l => A l c)) i j = z ∧
      |z| ≤ W := by
    intro k c i j
    rw [Matrix.updateCol_apply]
    split_ifs
    · exact hAint _ _
    · exact hM0i _ _
  obtain ⟨Q, hQ, hQb⟩ := det_int_bound M0 _ W hM0i
  have hDq : (Dn rows : ℚ) ≠ 0 := by exact_mod_cast (dn_pos rows).ne'
  have hQ0 : Q ≠ 0 := by
    intro h0; rw [h0] at hQ; push_cast at hQ
    exact hdet ((mul_eq_zero.1 hQ).resolve_left (pow_ne_zero _ hDq))
  have hQq : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ0
  have hW1 : (1 : ℤ) ≤ W := one_le_pow₀ (by norm_num)
  have hV : (s.factorial : ℤ) * W ^ s ≤ m.factorial * W ^ m :=
    mul_le_mul (by exact_mod_cast Nat.factorial_le hsm) (pow_le_pow_right₀ hW1 hsm)
      (by positivity) (by positivity)
  have hVm0 : (0 : ℤ) ≤ m.factorial * W ^ m := by positivity
  have hmW : (1 : ℤ) ≤ (m + 1) * W := by nlinarith
  have hBn : (((m + 1) * 2 ^ (2 * Kb rows) * (m.factorial * (2 ^ (2 * Kb rows)) ^ m) : ℕ) : ℤ)
      = (m + 1) * W * (m.factorial * W ^ m) := by push_cast; rfl
  have hBig : (m.factorial : ℤ) * W ^ m ≤ (m + 1) * W * (m.factorial * W ^ m) :=
    le_mul_of_one_le_left hVm0 hmW
  -- pivot entries as N / Q
  have hPkc : ∀ k c, ∃ N : ℤ, P k c = (N : ℚ) / Q ∧ |N| ≤ s.factorial * W ^ s := by
    intro k c
    obtain ⟨N, hN1, hN2⟩ := det_int_bound (M0.updateCol k (fun l => A l c)) _ W (hU k c)
    refine ⟨N, ?_, hN2⟩
    rw [hrep k c, ← hN1, ← hQ, mul_div_mul_left _ _ (pow_ne_zero _ hDq)]
  refine ⟨?_, ?_⟩
  · intro qr hq c
    obtain ⟨k, rfl⟩ := List.mem_iff_get.1 hq
    obtain ⟨N, hN1, hN2⟩ := hPkc k c
    show bitSize (P k c) ≤ _
    rw [hN1]
    unfold Bst
    refine bitSize_frac_le N Q hQ0 _ ?_ ?_ <;> rw [hBn]
    · exact hN2.trans (hV.trans hBig)
    · exact hQb.trans (hV.trans hBig)
  · intro r hr c
    obtain ⟨a, ha, hra⟩ := hOrest r hr
    have hrJ : ∀ l, (toF r : Fin m → ℚ) (J l) = 0 :=
      fun l => hR r hr (J l) (hP1 _ (List.get_mem _ _)).2
    have hrep2 := rest_rep A J P hP hJ a (toF r) (hspan ▸ hra) hrJ c
    choose za hza hzab using fun c => scaled_int ha c
    choose Nk hNk hNkb using fun k => hPkc k c
    have hval : (toF r : Fin m → ℚ) c =
        ((za c * Q - ∑ k, za (J k) * Nk k : ℤ) : ℚ) / ((Dz * Q : ℤ) : ℚ) := by
      rw [hrep2, eq_div_iff (by push_cast; exact mul_ne_zero hDq hQq)]
      push_cast
      rw [← hza c]
      simp only [← hza, hNk]
      rw [sub_mul, Finset.sum_mul]
      congr 1
      · simp only [hDz, Int.cast_natCast]; ring
      · refine Finset.sum_congr rfl fun k _ => ?_
        field_simp
        simp only [hDz, Int.cast_natCast]
    rw [hval]
    unfold Bst
    have hVs : (0 : ℤ) ≤ s.factorial * W ^ s := by positivity
    have hW0 : (0 : ℤ) ≤ W := by positivity
    have hDW : Dz ≤ W := by
      have := dn_le rows
      have h2 : (2 : ℤ) ^ Kb rows ≤ W := pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : Dz ≤ 2 ^ Kb rows := by rw [hDz]; exact_mod_cast this
      exact h3.trans h2
    have hD0 : (0 : ℤ) ≤ Dz := by rw [hDz]; positivity
    refine bitSize_frac_le _ _ (mul_ne_zero (by rw [hDz]; exact_mod_cast (dn_pos rows).ne') hQ0)
      _ ?_ ?_ <;> rw [hBn]
    · have e1 : |za c * Q - ∑ k, za (J k) * Nk k| ≤ W * (s.factorial * W ^ s) +
          ∑ _k : Fin s, W * (s.factorial * W ^ s) := by
        refine (abs_sub _ _).trans (add_le_add ?_ ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun k _ => ?_)))
        · rw [abs_mul]; exact mul_le_mul (hzab c) hQb (abs_nonneg _) hW0
        · rw [abs_mul]; exact mul_le_mul (hzab _) (hNkb k) (abs_nonneg _) hW0
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1
      refine e1.trans ?_
      have : (s : ℤ) ≤ m := by exact_mod_cast hsm
      have h4 : W * (s.factorial * W ^ s) ≤ W * (m.factorial * W ^ m) :=
        mul_le_mul_of_nonneg_left hV hW0
      calc W * (s.factorial * W ^ s) + (s : ℤ) * (W * (s.factorial * W ^ s))
          = ((s : ℤ) + 1) * (W * (s.factorial * W ^ s)) := by ring
        _ ≤ ((m : ℤ) + 1) * (W * (m.factorial * W ^ m)) :=
          mul_le_mul (by linarith) h4 (by positivity) (by positivity)
        _ = _ := by ring
    · rw [abs_mul, abs_of_nonneg hD0]
      have h4 : Dz * |Q| ≤ W * (m.factorial * W ^ m) :=
        mul_le_mul hDW (hQb.trans hV) (abs_nonneg _) hW0
      nlinarith


/-! ## Step D: tick counting -/

def Cost {α : Type} (p : StateM ℕ α) (c : ℕ) : Prop := ∀ t, (p.run t).2 ≤ t + c

theorem cost_mono {α : Type} {p : StateM ℕ α} {c c' : ℕ} (h : Cost p c) (hc : c ≤ c') :
    Cost p c' := fun t => (h t).trans (by omega)
theorem cost_pure {α : Type} (a : α) : Cost (pure a : StateM ℕ α) 0 := fun t => Nat.le_add_right _ _
theorem cost_tick (c : ℕ) : Cost (tick c) c := fun _ => le_refl _
theorem cost_bind {α β : Type} {p : StateM ℕ α} {f : α → StateM ℕ β} {a : α} {c1 c2 : ℕ}
    (hp : Cost p c1) (hv : Val p a) (hf : Cost (f a) c2) : Cost (p >>= f) (c1 + c2) := by
  intro t; rw [run_bind', hv t]; have := hp t; have := hf (p.run t).2; omega
theorem cost_qadd (a b : ℚ) : Cost (qadd a b) (opCost a b) := fun _ => le_refl _
theorem cost_qsub (a b : ℚ) : Cost (qsub a b) (opCost a b) := fun _ => le_refl _
theorem cost_qmul (a b : ℚ) : Cost (qmul a b) (opCost a b) := fun _ => le_refl _
theorem cost_qdiv (a b : ℚ) : Cost (qdiv a b) (opCost a b) := fun _ => le_refl _
theorem cost_qeq (a b : ℚ) : Cost (qeq a b) (opCost a b) := fun _ => le_refl _
theorem cost_uAt {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) (j : Fin m) :
    Cost (uAt u i j) (bitSize (u i j) + 1) := fun _ => le_refl _

theorem cost_mapM {α β : Type} (f : α → StateM ℕ β) (g : α → β) (hv : ∀ a, Val (f a) (g a))
    (c : ℕ) : ∀ l : List α, (∀ a ∈ l, Cost (f a) c) → Cost (l.mapM f) (l.length * c)
  | [], _ => by simpa using cost_pure ([] : List β)
  | a :: l, h => by
    rw [List.mapM_cons]
    refine cost_mono (cost_bind (c2 := l.length * c + 0) (h a (by simp)) (hv a) ?_)
      (le_of_eq (by simp only [List.length_cons]; ring))
    exact cost_bind (cost_mapM f g hv c l fun b hb => h b (List.mem_cons_of_mem _ hb))
      (val_mapM f g hv l) (cost_pure _)

theorem cost_bind_mapM {α β γ : Type} (f : α → StateM ℕ β) (g : α → β)
    (hv : ∀ a, Val (f a) (g a)) (c : ℕ) (l : List α) (h : ∀ a ∈ l, Cost (f a) c)
    {k : List β → StateM ℕ γ} {c2 : ℕ} (hk : Cost (k (l.map g)) c2) :
    Cost (l.mapM f >>= k) (l.length * c + c2) :=
  cost_bind (cost_mapM f g hv c l h) (val_mapM f g hv l) hk

theorem cost_foldlM {α β : Type} (f : β → α → StateM ℕ β) (g : β → α → β)
    (hv : ∀ b a, Val (f b a) (g b a)) (c : ℕ) :
    ∀ (l : List α) (b : β), (∀ k (hk : k < l.length), Cost (f ((l.take k).foldl g b) l[k]) c) →
      Cost (l.foldlM f b) (l.length * c)
  | [], b, _ => by simpa using cost_pure b
  | a :: l, b, h => by
    rw [List.foldlM_cons]
    have h0 := h 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.getElem_cons_zero] at h0
    refine cost_mono (cost_bind (c2 := l.length * c) h0 (hv b a) ?_)
      (le_of_eq (by simp only [List.length_cons]; ring))
    exact cost_foldlM f g hv c l (g b a) fun k hk => by
      have := h (k + 1) (by simp; omega)
      simpa [List.take_succ_cons, List.foldl_cons] using this

theorem cost_filterMapM {α β : Type} (f : α → StateM ℕ (Option β)) (g : α → Option β)
    (hv : ∀ a, Val (f a) (g a)) (c : ℕ) (hc : ∀ a, Cost (f a) c) :
    ∀ l : List α, Cost (l.filterMapM f) (l.length * c)
  | [] => by simpa using cost_pure ([] : List β)
  | a :: l => by
    rw [List.filterMapM_cons]
    refine cost_mono (cost_bind (hc a) (hv a) (c2 := l.length * c) ?_)
      (le_of_eq (by simp only [List.length_cons]; ring))
    cases g a with
    | none => exact cost_filterMapM f g hv c hc l
    | some b =>
      refine cost_mono (cost_bind (c2 := 0) (cost_filterMapM f g hv c hc l)
        (val_filterMapM f g hv l) ?_) (by simp)
      exact cost_pure _

theorem bitSize_zero : bitSize 0 = 2 := by unfold bitSize; simp

theorem size_mul_le' (x y : ℕ) : Nat.size (x * y) ≤ Nat.size x + Nat.size y := by
  rw [Nat.size_le, pow_add]
  exact mul_lt_mul'' (Nat.lt_size_self x) (Nat.lt_size_self y) (Nat.zero_le _) (Nat.zero_le _)

theorem bitSize_mul_le (a b : ℚ) : bitSize (a * b) ≤ bitSize a + bitSize b := by
  have e : a * b = ((a.num * b.num : ℤ) : ℚ) / (((a.den * b.den : ℕ) : ℤ) : ℚ) := by
    push_cast
    rw [mul_div_mul_comm, Rat.num_div_den, Rat.num_div_den]
  rw [e]
  refine (bitSize_intdiv_le _ _ (by positivity)).trans ?_
  rw [Int.natAbs_mul, Int.natAbs_natCast]
  have := size_mul_le' a.num.natAbs b.num.natAbs
  have := size_mul_le' a.den b.den
  unfold bitSize; omega

theorem getD_bound (r : List ℚ) (c B : ℕ) (h : ∀ e ∈ r, bitSize e ≤ B) (hB : 2 ≤ B) :
    bitSize (r.getD c 0) ≤ B := by
  rw [List.getD_eq_getElem?_getD]
  cases hc : r[c]? with
  | none => simpa [bitSize_zero] using hB
  | some e => exact h e (List.mem_of_getElem? hc)

theorem bst_ge (m K : ℕ) : 2 ≤ Bst m K := by
  unfold Bst
  have : 0 < Nat.size ((m + 1) * 2 ^ (2 * K) * (m.factorial * (2 ^ (2 * K)) ^ m)) :=
    Nat.size_pos.2 (by positivity)
  omega

def Bnd {m : ℕ} (B : ℕ) (st : List (Fin m × List ℚ) × List (List ℚ)) : Prop :=
  (∀ qr ∈ st.1, ∀ e ∈ qr.2, bitSize e ≤ B) ∧ (∀ r ∈ st.2, ∀ e ∈ r, bitSize e ≤ B)

theorem mem_toF {m : ℕ} (r : List ℚ) (hr : r.length = m) (e : ℚ) (he : e ∈ r) :
    ∃ c : Fin m, toF r c = e := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  exact ⟨⟨i, hr ▸ hi⟩, by simp [toF, List.getD_eq_getElem?_getD, hi]⟩

theorem bnd_of_inv {m : ℕ} (rows : List (Fin m → ℚ)) (S : Fin m → Prop)
    (st : List (Fin m × List ℚ) × List (List ℚ)) (hK : KInv rows S st) (hP : PInv rows st) :
    Bnd (Bst m (Kb rows)) st := by
  have hsb := stage_bound rows S st hK hP
  refine ⟨fun qr hq e he => ?_, fun r hr e he => ?_⟩
  · obtain ⟨c, rfl⟩ := mem_toF qr.2 (hK.1 qr hq) e he
    exact hsb.1 qr hq c
  · obtain ⟨c, rfl⟩ := mem_toF r (hK.2.1 r hr) e he
    exact hsb.2 r hr c

theorem kinv_init {m : ℕ} (rows : List (Fin m → ℚ)) :
    KInv rows (fun _ => False) ([], rows.map fun r => (List.finRange m).map r) := by
  refine ⟨by simp, ?_, by simp, by simp, by simp, fun _ _ _ hc => hc.elim, ?_⟩
  · intro r hr
    obtain ⟨r0, _, rfl⟩ := List.mem_map.mp hr
    simp
  · intro d _ hd r hr
    have := hd _ (List.mem_map.2 ⟨r, hr, rfl⟩)
    unfold dotL at this
    simpa only [getD_map_finRange] using this

theorem fpV_len (c : ℕ) : ∀ (l : List (List ℚ)) (p : List ℚ) (rest : List (List ℚ)),
    fpV c l = some (p, rest) → rest.length + 1 = l.length
  | [], p, rest, h => by simp [fpV] at h
  | r :: rs, p, rest, h => by
    rw [fpV] at h
    by_cases hz : r.getD c 0 = 0
    · rw [if_pos (by simpa using hz)] at h
      rcases hr : fpV c rs with _ | ⟨p1, rest1⟩
      · simp [hr] at h
      · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have := fpV_len c rs p1 rest1 hr
        simp; omega
    · rw [if_neg (by simpa using hz)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp

theorem stepV_len2 {m : ℕ} (st : List (Fin m × List ℚ) × List (List ℚ)) (c : Fin m) :
    (stepV st c).2.length ≤ st.2.length := by
  unfold stepV
  rcases h : fpV c.val st.2 with _ | ⟨p, rest⟩
  · simp
  · have := fpV_len c.val st.2 p rest h
    simp; omega

theorem foldl_len2 {m : ℕ} : ∀ (l : List (Fin m)) (st : List (Fin m × List ℚ) × List (List ℚ)),
    (l.foldl stepV st).2.length ≤ st.2.length
  | [], st => le_refl _
  | c :: l, st => (foldl_len2 l (stepV st c)).trans (stepV_len2 st c)

theorem cost_findPivot (c B : ℕ) : ∀ l : List (List ℚ), (∀ r ∈ l, bitSize (r.getD c 0) ≤ B) →
    Cost (kernelDir.findPivot c l) (l.length * (1 + (B + 3) ^ 2))
  | [], _ => by rw [kernelDir.findPivot]; exact cost_mono (cost_pure _) (Nat.zero_le _)
  | r :: rs, h => by
    rw [kernelDir.findPivot]
    have hr : opCost (r.getD c 0) 0 ≤ (B + 3) ^ 2 := by
      unfold opCost; rw [bitSize_zero]
      exact Nat.pow_le_pow_left (by have := h r (by simp); omega) 2
    have ih := cost_findPivot c B rs (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    refine cost_mono (cost_bind (cost_tick 1) (val_tick _)
      (cost_bind (cost_qeq _ _) (val_qeq _ _) (c2 := rs.length * (1 + (B + 3) ^ 2)) ?_)) ?_
    · cases decide (r.getD c 0 = 0)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact cost_mono (cost_pure _) (Nat.zero_le _)
      · simp only [↓reduceIte]
        refine cost_mono (cost_bind ih (val_findPivot c rs) (c2 := 0) ?_) (by omega)
        cases fpV c rs with
        | none => exact cost_pure _
        | some pr => exact cost_pure _
    · simp only [List.length_cons]; nlinarith [hr]

def Eb (B : ℕ) : ℕ := 1 + (2 * B + 1) ^ 2 + (3 * B + 1) ^ 2

theorem cost_elim (c : ℕ) (p r : List ℚ) (B : ℕ) (hB : 2 ≤ B) (hp : ∀ e ∈ p, bitSize e ≤ B)
    (hr : ∀ e ∈ r, bitSize e ≤ B) : Cost (kernelDir.elim c p r) (r.length * Eb B) := by
  unfold kernelDir.elim
  have hrc := getD_bound r c B hr hB
  refine cost_mono (cost_mapM _ (fun ab => ab.1 - r.getD c 0 * ab.2) (fun ab => by
    rcases ab with ⟨a, b⟩
    exact val_bind (val_tick _) (val_bind (val_qmul _ _) (val_qsub _ _))) (Eb B) _
    (fun ab hab => ?_)) ?_
  · rcases ab with ⟨a, b⟩
    obtain ⟨ha, hb⟩ := List.of_mem_zip hab
    have h1 := hr a ha
    have h2 := hp b hb
    have h3 := bitSize_mul_le (r.getD c 0) b
    refine cost_mono (cost_bind (cost_tick 1) (val_tick _)
      (cost_bind (cost_qmul _ _) (val_qmul _ _) (cost_qsub _ _))) ?_
    unfold Eb opCost
    have e1 : (bitSize (r.getD c 0) + bitSize b + 1) ^ 2 ≤ (2 * B + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have e2 : (bitSize a + bitSize (r.getD c 0 * b) + 1) ^ 2 ≤ (3 * B + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    omega
  · rw [List.length_zip]
    exact Nat.mul_le_mul_right _ (min_le_left _ _)

def Cs (m R B : ℕ) : ℕ :=
  1 + R * (1 + (B + 3) ^ 2) + m * (1 + (2 * B + 1) ^ 2) + m * (m * Eb B) + R * (m * Eb B)

def KC (m R K : ℕ) : ℕ :=
  R * (m * (K + 1)) + (m * Cs m R (Bst m K) + ((m + 1) + m * (1 + (Bst m K + 3) ^ 2)))

theorem cost_bind_foldlM {α β γ : Type} (f : β → α → StateM ℕ β) (g : β → α → β)
    (hv : ∀ b a, Val (f b a) (g b a)) (c : ℕ) (l : List α) (b : β)
    (h : ∀ k (hk : k < l.length), Cost (f ((l.take k).foldl g b) l[k]) c)
    {k : β → StateM ℕ γ} {c2 : ℕ} (hk : Cost (k (l.foldl g b)) c2) :
    Cost (l.foldlM f b >>= k) (l.length * c + c2) :=
  cost_bind (cost_foldlM f g hv c l b h) (val_foldlM f g hv l b) hk

theorem stage_inv {m : ℕ} (rows : List (Fin m → ℚ)) (k : ℕ) :
    KInv rows (fun x => False ∨ x ∈ (List.finRange m).take k)
      (((List.finRange m).take k).foldl stepV ([], rows.map fun r => (List.finRange m).map r)) ∧
    PInv rows
      (((List.finRange m).take k).foldl stepV ([], rows.map fun r => (List.finRange m).map r)) :=
  ⟨kinv_foldl rows _ _ _ ((List.take_sublist _ _).nodup (List.nodup_finRange m)) (fun _ _ h => h)
    (kinv_init rows), pinv_foldl rows _ _ (pinv_init rows)⟩

theorem not_mem_take_finRange {m : ℕ} (k : ℕ) (hk : k < (List.finRange m).length) :
    ¬ (False ∨ (List.finRange m)[k] ∈ (List.finRange m).take k) := by
  rintro (h | h)
  · exact h
  · obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.1 h
    rw [List.getElem_take] at he
    have := ((List.nodup_finRange m).getElem_inj_iff).1 he
    simp at hi; omega

theorem cost_kernelDir {m : ℕ} (rows : List (Fin m → ℚ)) :
    Cost (kernelDir rows) (KC m rows.length (Kb rows)) := by
  have hB : 2 ≤ Bst m (Kb rows) := bst_ge m (Kb rows)
  unfold kernelDir KC
  refine cost_bind_mapM _ (fun (r : Fin m → ℚ) => (List.finRange m).map r)
    (fun (r : Fin m → ℚ) => val_mapM _ (fun c => r c)
      (fun c => val_bind (val_tick _) (val_pure (r c))) _) _ rows (fun r hr => ?_) ?_
  · refine cost_mono (cost_mapM _ (fun c => r c)
      (fun c => val_bind (val_tick _) (val_pure (r c))) (Kb rows + 1) _ (fun c _ => ?_)) (by simp)
    exact cost_mono (cost_bind (cost_tick _) (val_tick _) (cost_pure _))
      (by have := ent_le hr c; omega)
  have hlen := List.length_finRange (n := m)
  refine cost_mono (cost_bind_foldlM _ stepV (fun st c => ?_) (Cs m rows.length (Bst m (Kb rows)))
    _ _ (fun k hk => ?_) (c2 := (m + 1) + m * (1 + (Bst m (Kb rows) + 3) ^ 2)) ?_)
    (by rw [hlen])
  · refine val_bind (val_tick _) ?_
    refine val_bind (val_findPivot _ _) ?_
    unfold stepV
    cases fpV c.val st.2 with
    | none => exact val_pure _
    | some pr =>
      obtain ⟨p, rest⟩ := pr
      dsimp only
      refine val_bind (val_mapM _ (fun a => a / p.getD c.val 0)
        (fun a => val_bind (val_tick _) (val_qdiv _ _)) _) ?_
      refine val_bind (val_mapM _
        (fun qr => (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2))
        (fun qr => ?_) _) ?_
      · rcases qr with ⟨q, r⟩
        exact val_bind (val_elim _ _ _) (val_pure _)
      · refine val_bind (val_mapM _ _ (fun r => val_elim _ _ _) _) ?_
        exact val_pure _
  · -- one elimination step
    set B := Bst m (Kb rows) with hBd
    obtain ⟨hK, hPI⟩ := stage_inv rows k
    set c := (List.finRange m)[k] with hc
    set st := ((List.finRange m).take k).foldl stepV
      ([], rows.map fun r => (List.finRange m).map r) with hst
    have hnc := not_mem_take_finRange k hk
    have hb := bnd_of_inv rows _ st hK hPI
    have hb' := bnd_of_inv rows _ (stepV st c) (kinv_step rows _ st c hnc hK) (pinv_step rows st c hPI)
    have hn1 : st.1.length ≤ m := by have := hK.2.2.2.2.1.length_le_card; simpa using this
    have hn2 : st.2.length ≤ rows.length := by
      have := foldl_len2 ((List.finRange m).take k) ([], rows.map fun r => (List.finRange m).map r)
      simpa using this
    refine cost_mono (c := 1 + (st.2.length * (1 + (B + 3) ^ 2) + (m * (1 + (2 * B + 1) ^ 2) +
      (st.1.length * (m * Eb B) + (st.2.length * (m * Eb B) + 0))))) ?_ ?_
    · refine cost_bind (cost_tick 1) (val_tick _) ?_
      refine cost_bind (cost_findPivot c.val B st.2 (fun r hr => getD_bound r _ B (hb.2 r hr) hB))
        (val_findPivot _ _) ?_
      rcases hfp : fpV c.val st.2 with _ | ⟨p, rest⟩
      · exact cost_mono (cost_pure _) (Nat.zero_le _)
      · obtain ⟨hpm, -, hrest, -⟩ := fpV_some c.val st.2 p rest hfp
        have hpl : p.length = m := hK.2.1 p hpm
        have hrl := fpV_len c.val st.2 p rest hfp
        have hp'b : ∀ e ∈ p.map (fun a => a / p.getD c.val 0), bitSize e ≤ B := by
          refine hb'.1 (c, p.map fun a => a / p.getD c.val 0) ?_
          simp [stepV, hfp]
        have hpc := getD_bound p c.val B (hb.2 p hpm) hB
        dsimp only
        refine cost_mono (cost_bind_mapM _ (fun a => a / p.getD c.val 0)
          (fun a => val_bind (val_tick _) (val_qdiv _ _)) (1 + (2 * B + 1) ^ 2) p (fun a ha => ?_)
          (c2 := st.1.length * (m * Eb B) + (st.2.length * (m * Eb B) + 0)) ?_)
          (by rw [hpl])
        · refine cost_mono (cost_bind (cost_tick 1) (val_tick _) (cost_qdiv _ _)) ?_
          unfold opCost
          have := hb.2 p hpm a ha
          have : (bitSize a + bitSize (p.getD c.val 0) + 1) ^ 2 ≤ (2 * B + 1) ^ 2 :=
            Nat.pow_le_pow_left (by omega) 2
          omega
        refine cost_bind_mapM _
          (fun qr => (qr.1, elimV c.val (p.map fun a => a / p.getD c.val 0) qr.2))
          (fun qr => by rcases qr with ⟨q, r⟩; exact val_bind (val_elim _ _ _) (val_pure _))
          (m * Eb B) st.1 (fun qr hq => ?_) ?_
        · rcases qr with ⟨q, r⟩
          have hrl' : r.length = m := hK.1 _ hq
          refine cost_mono (cost_bind (cost_elim c.val _ r B hB hp'b (hb.1 _ hq))
            (val_elim _ _ _) (cost_pure _)) (by rw [hrl', Nat.add_zero])
        refine cost_mono (cost_bind_mapM _ _ (fun r => val_elim _ _ _) (m * Eb B) rest
          (fun r hr => ?_) (cost_pure _)) ?_
        · have hr2 := hrest r hr
          exact cost_mono (cost_elim c.val _ r B hB hp'b (hb.2 r hr2)) (by rw [hK.2.1 r hr2])
        · have : rest.length ≤ st.2.length := by omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_right _ this) _
    · unfold Cs
      have e1 := Nat.mul_le_mul_right (1 + (B + 3) ^ 2) hn2
      have e2 := Nat.mul_le_mul_right (m * Eb B) hn1
      have e3 := Nat.mul_le_mul_right (m * Eb B) hn2
      omega
  · -- final kernel vector
    obtain ⟨hKf, hPf⟩ := stage_inv rows m
    rw [List.take_of_length_le (by rw [hlen])] at hKf hPf
    have hbf := bnd_of_inv rows _ _ hKf hPf
    generalize (List.finRange m).foldl stepV
      ([], rows.map fun r => (List.finRange m).map r) = st at hbf
    dsimp only
    refine cost_bind (cost_tick _) (val_tick _) ?_
    cases (List.finRange m).find? (fun c => !(st.1.any fun pr => pr.1 == c)) with
    | none => exact cost_mono (cost_pure _) (Nat.zero_le _)
    | some f =>
      refine cost_mono (cost_bind_mapM _ (dV st.1 f) (fun c => ?_) (1 + (Bst m (Kb rows) + 3) ^ 2)
        _ (fun c _ => ?_) (cost_pure _)) (by rw [hlen]; omega)
      · refine val_bind (val_tick _) ?_
        unfold dV
        by_cases hc : c = f
        · rw [if_pos hc, if_pos hc]
          exact val_pure _
        · rw [if_neg hc, if_neg hc]
          cases st.1.find? (fun pr => pr.1 == c) with
          | none => exact val_pure _
          | some pr =>
            obtain ⟨q, r⟩ := pr
            exact val_qsub _ _
      · refine cost_bind (cost_tick 1) (val_tick _) ?_
        by_cases hc : c = f
        · rw [if_pos hc]; exact cost_mono (cost_pure _) (Nat.zero_le _)
        · rw [if_neg hc]
          split
          next q r hfd =>
            refine cost_mono (cost_qsub _ _) ?_
            have hm := List.mem_of_find?_eq_some hfd
            have := getD_bound r f.val _ (hbf.1 _ hm) hB
            unfold opCost; rw [bitSize_zero]
            exact Nat.pow_le_pow_left (by omega) 2
          next => exact cost_mono (cost_pure _) (Nat.zero_le _)


/-! ## Step E: cost of findSolution and the polynomial bound -/

theorem bitSize_neg (e : ℚ) : bitSize (-e) = bitSize e := by unfold bitSize; simp
theorem bitSize_one : bitSize 1 = 3 := by unfold bitSize; simp

theorem bst_ge3 (m K : ℕ) : 3 ≤ Bst m K := by
  unfold Bst
  have : 0 < Nat.size ((m + 1) * 2 ^ (2 * K) * (m.factorial * (2 ^ (2 * K)) ^ m)) :=
    Nat.size_pos.2 (by positivity)
  omega

theorem kernelDirV_bound {m : ℕ} (rows : List (Fin m → ℚ)) (d : Fin m → ℚ)
    (h : kernelDirV rows = some d) (j : Fin m) : bitSize (d j) ≤ Bst m (Kb rows) := by
  have hlen := List.length_finRange (n := m)
  obtain ⟨hKf, hPf⟩ := stage_inv rows m
  rw [List.take_of_length_le (by rw [hlen])] at hKf hPf
  have hbf := bnd_of_inv rows _ _ hKf hPf
  have hB := bst_ge3 m (Kb rows)
  unfold kernelDirV finalV at h
  generalize (List.finRange m).foldl stepV
    ([], rows.map fun r => (List.finRange m).map r) = st at hbf h
  split at h
  next => simp at h
  next f _ =>
    obtain rfl := Option.some.inj h
    beta_reduce
    rw [getD_map_finRange]
    unfold dV
    split_ifs
    · rw [bitSize_one]; exact hB
    · split
      next q r hfd =>
        rw [zero_sub, bitSize_neg]
        exact getD_bound r f.val _ (hbf.1 _ (List.mem_of_find?_eq_some hfd)) (by omega)
      next => rw [bitSize_zero]; omega

theorem kb_le {m : ℕ} (rows : List (Fin m → ℚ)) (M : ℕ) (h : ∀ r ∈ rows, ∀ c, bitSize (r c) ≤ M) :
    Kb rows ≤ rows.length * (m * M) := by
  unfold Kb
  induction rows with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 : ∑ c, bitSize (r c) ≤ m * M := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c => bitSize (r c)) M
        (fun c _ => h r (by simp) c)
      simpa using this
    have h2 := ih (fun r' hr' c => h r' (List.mem_cons_of_mem _ hr') c)
    have e : (rs.length + 1) * (m * M) = rs.length * (m * M) + m * M := by ring
    omega

theorem bitSize_le_input {n m : ℕ} (u : Fin n → Fin m → ℚ) (i : Fin n) (j : Fin m) :
    bitSize (u i j) ≤ inputSize u := by
  have h1 : bitSize (u i j) ≤ ∑ j', bitSize (u i j') :=
    Finset.single_le_sum (f := fun j' => bitSize (u i j')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  have h2 : ∑ j', bitSize (u i j') ≤ ∑ i', ∑ j', bitSize (u i' j') :=
    Finset.single_le_sum (f := fun i' => ∑ j', bitSize (u i' j')) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  unfold inputSize; omega

theorem sysRows_entry {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) :
    ∀ r ∈ sysRows u T, ∀ c, bitSize (r c) ≤ inputSize u + 3 := by
  intro r hr c
  unfold sysRows at hr
  rcases List.mem_append.1 hr with h | h
  · obtain ⟨i, -, rfl⟩ := List.mem_map.1 h
    unfold urowV
    rw [getD_map_finRange]
    have := bitSize_le_input u i c
    omega
  · obtain ⟨j, -, hj⟩ := List.mem_filterMap.1 h
    split_ifs at hj
    · obtain rfl := Option.some.inj hj
      rw [Pi.single_apply]
      split_ifs
      · rw [bitSize_one]; omega
      · rw [bitSize_zero]; omega

theorem sysRows_len {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) :
    (sysRows u T).length ≤ n + m := by
  unfold sysRows
  rw [List.length_append, List.length_map, List.length_finRange]
  have := List.length_filterMap_le (fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    (List.finRange m)
  rw [List.length_finRange] at this
  omega

theorem cost_findSolution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) :
    Cost (findSolution u T x) (n * (m * (inputSize u + 1)) + (m * 1 +
      (KC m (sysRows u T).length (Kb (sysRows u T)) +
        (m * ((∑ j, bitSize (x j)) + Bst m (Kb (sysRows u T)) + 1) ^ 2 + 0)))) := by
  unfold findSolution
  refine cost_mono (cost_bind_mapM (c2 := m * 1 + (KC m (sysRows u T).length (Kb (sysRows u T)) +
      (m * ((∑ j, bitSize (x j)) + Bst m (Kb (sysRows u T)) + 1) ^ 2 + 0)))
    _ (urowV u) ?hv (m * (inputSize u + 1)) (List.finRange n) ?hc ?hk)
    (by rw [List.length_finRange])
  case hv =>
    intro i
    exact val_bind (val_mapM _ (fun j => u i j) (fun j => val_uAt u i j) _) (val_pure _)
  case hc =>
    intro i _
    refine cost_mono (cost_bind (cost_mapM _ (fun j => u i j) (fun j => val_uAt u i j)
      (inputSize u + 1) _ (fun j _ => cost_mono (cost_uAt u i j)
        (by have := bitSize_le_input u i j; omega)))
      (val_mapM _ _ (fun j => val_uAt u i j) _) (cost_pure _)) (by simp)
  refine cost_bind (cost_mono (cost_filterMapM _
    (fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none)
    (fun j => val_bind (val_tick _) (val_pure _)) 1
    (fun j => cost_mono (cost_bind (cost_tick 1) (val_tick _) (cost_pure _)) (le_refl _)) _)
    (by rw [List.length_finRange]))
    (val_filterMapM _ _ (fun j => val_bind (val_tick _) (val_pure _)) _) ?_
  refine cost_bind (cost_kernelDir (sysRows u T)) (val_kernelDir _) ?_
  split
  next hk => exact cost_mono (cost_pure _) (Nat.zero_le _)
  next d hk =>
    refine cost_mono (cost_bind_mapM _ (fun j => x j + d j) (fun j => val_qadd _ _)
      (((∑ j, bitSize (x j)) + Bst m (Kb (sysRows u T)) + 1) ^ 2) _ (fun j _ => ?_)
      (cost_pure _)) (by rw [List.length_finRange])
    refine cost_mono (cost_qadd _ _) ?_
    unfold opCost
    have h1 : bitSize (x j) ≤ ∑ j, bitSize (x j) :=
      Finset.single_le_sum (f := fun j => bitSize (x j)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have h2 := kernelDirV_bound (sysRows u T) d hk j
    exact Nat.pow_le_pow_left (by omega) 2

theorem two_pow_gt (k : ℕ) : k < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ]; omega

theorem bst_le (m K : ℕ) : Bst m K ≤ 2 * (m + 2 + 2 * K + m * m + 2 * (K * m)) + 1 := by
  unfold Bst
  have f1 : m.factorial ≤ (2 ^ m) ^ m :=
    (Nat.factorial_le_pow m).trans (Nat.pow_le_pow_left (two_pow_gt m).le m)
  have h1 : (m + 1) * 2 ^ (2 * K) * (m.factorial * (2 ^ (2 * K)) ^ m) ≤
      2 ^ (m + 1 + 2 * K + m * m + 2 * (K * m)) := by
    have e : (2 : ℕ) ^ (m + 1 + 2 * K + m * m + 2 * (K * m)) =
        2 ^ (m + 1) * 2 ^ (2 * K) * ((2 ^ m) ^ m * (2 ^ (2 * K)) ^ m) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1; ring
    rw [e]
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (two_pow_gt _).le) (Nat.mul_le_mul_right _ f1)
  have h2 := Nat.size_le_size h1
  rw [Nat.size_pow] at h2
  omega

def Fb (b : ℕ) : ℕ :=
  b * (b * (b + 1)) + (b * 1 + ((b * (b * (b + 1)) + (b * (1 + b * (1 + (b + 3) ^ 2) +
    b * (1 + (2 * b + 1) ^ 2) + b * (b * (1 + (2 * b + 1) ^ 2 + (3 * b + 1) ^ 2)) +
    b * (b * (1 + (2 * b + 1) ^ 2 + (3 * b + 1) ^ 2))) + ((b + 1) + b * (1 + (b + 3) ^ 2)))) +
    (b * (b + b + 1) ^ 2 + 0)))

theorem fb_le (b : ℕ) (hb : 1 ≤ b) : Fb b ≤ 200 * b ^ 5 := by
  have h0 : 1 ≤ b ^ 5 := Nat.one_le_pow _ _ hb
  have h1 : b ≤ b ^ 5 := Nat.le_self_pow (by norm_num) b
  have h2 : b ^ 2 ≤ b ^ 5 := Nat.pow_le_pow_right hb (by norm_num)
  have h3 : b ^ 3 ≤ b ^ 5 := Nat.pow_le_pow_right hb (by norm_num)
  have h4 : b ^ 4 ≤ b ^ 5 := Nat.pow_le_pow_right hb (by norm_num)
  unfold Fb
  ring_nf
  omega

theorem cost_poly {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) :
    Cost (findSolution u T x)
      (200 * 100 ^ 5 * (inputSize u + ∑ j, bitSize (x j) + 1) ^ 20) := by
  refine cost_mono (cost_findSolution u T x) ?_
  set N := inputSize u + ∑ j, bitSize (x j) + 1 with hN
  set I := inputSize u with hI
  set X := ∑ j, bitSize (x j) with hX
  set R := (sysRows u T).length with hR
  set K := Kb (sysRows u T) with hK
  set B := Bst m K with hBd
  have hN1 : 1 ≤ N := by omega
  have hnm : n + m ≤ I := by rw [hI]; unfold inputSize; omega
  have p1 : N ≤ N ^ 4 := Nat.le_self_pow (by norm_num) N
  have p2 : N ^ 2 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by norm_num)
  have p3 : N ^ 3 ≤ N ^ 4 := Nat.pow_le_pow_right hN1 (by norm_num)
  have hRl : R ≤ N := by have := sysRows_len u T; omega
  have hKl : K ≤ 4 * N ^ 3 := by
    have h0 : K ≤ R * (m * (I + 3)) := kb_le (sysRows u T) (inputSize u + 3) (sysRows_entry u T)
    have e1 : R * (m * (I + 3)) ≤ N * (N * (4 * N)) :=
      Nat.mul_le_mul hRl (Nat.mul_le_mul (by omega) (by omega))
    have e2 : N * (N * (4 * N)) = 4 * N ^ 3 := by ring
    omega
  have hBl : B ≤ 100 * N ^ 4 := by
    have := bst_le m K
    have e1 : K * m ≤ 4 * N ^ 3 * N := Nat.mul_le_mul hKl (by omega)
    have e2 : m * m ≤ N * N := Nat.mul_le_mul (by omega) (by omega)
    have e3 : 4 * N ^ 3 * N = 4 * N ^ 4 := by ring
    have e4 : N * N = N ^ 2 := by ring
    omega
  set b := 100 * N ^ 4 with hb
  have hb1 : 1 ≤ b := by have := Nat.one_le_pow 4 N hN1; omega
  have hn : n ≤ b := by omega
  have hm : m ≤ b := by omega
  have hRb : R ≤ b := by omega
  have hKb : K ≤ b := by omega
  have hIb : I ≤ b := by omega
  have hXb : X ≤ b := by omega
  have hmain : n * (m * (I + 1)) + (m * 1 + (KC m R K + (m * (X + B + 1) ^ 2 + 0))) ≤ Fb b := by
    unfold KC Cs Eb Fb
    rw [← hBd]
    gcongr
  calc n * (m * (I + 1)) + (m * 1 + (KC m R K + (m * (X + B + 1) ^ 2 + 0))) ≤ Fb b := hmain
    _ ≤ 200 * b ^ 5 := fb_le b hb1
    _ = 200 * 100 ^ 5 * N ^ 20 := by rw [hb]; ring


/-! ## reachable_step_polytime (bf4b12e9) -/

theorem cost_qlt (a b : ℚ) : Cost (qlt a b) (opCost a b) := fun _ => le_refl _

theorem size_add_le' (x y : ℕ) : Nat.size (x + y) ≤ Nat.size x + Nat.size y + 1 := by
  rw [Nat.size_le]
  have hx := Nat.lt_size_self x
  have hy := Nat.lt_size_self y
  have e1 : 2 ^ Nat.size x ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : 2 ^ Nat.size y ≤ 2 ^ (Nat.size x + Nat.size y) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]; omega

theorem bitSize_add_le (a b : ℚ) : bitSize (a + b) ≤ 2 * (bitSize a + bitSize b) := by
  have hQ : ((a.den : ℤ) * b.den) ≠ 0 := by positivity
  have e : a + b = ((a.num * b.den + b.num * a.den : ℤ) : ℚ) / ((a.den * b.den : ℤ) : ℚ) := by
    rw [eq_div_iff (by exact_mod_cast hQ)]
    push_cast
    have ha : (a.num : ℚ) = a * a.den := (Rat.mul_den_eq_num a).symm
    have hb : (b.num : ℚ) = b * b.den := (Rat.mul_den_eq_num b).symm
    rw [ha, hb]; ring
  rw [e]
  refine (bitSize_intdiv_le _ _ hQ).trans ?_
  have h1 : (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs ≤
      a.num.natAbs * b.den + b.num.natAbs * a.den := by
    refine (Int.natAbs_add_le _ _).trans ?_
    simp [Int.natAbs_mul]
  have h2 : ((a.den : ℤ) * b.den).natAbs = a.den * b.den := by simp [Int.natAbs_mul]
  rw [h2]
  have s1 := Nat.size_le_size h1
  have s2 := size_add_le' (a.num.natAbs * b.den) (b.num.natAbs * a.den)
  have s3 := size_mul_le' a.num.natAbs b.den
  have s4 := size_mul_le' b.num.natAbs a.den
  have s5 := size_mul_le' a.den b.den
  unfold bitSize
  omega

theorem bitSize_sub_le (a b : ℚ) : bitSize (a - b) ≤ 2 * (bitSize a + bitSize b) := by
  rw [sub_eq_add_neg]
  have := bitSize_add_le a (-b)
  rw [bitSize_neg] at this
  exact this

theorem bitSize_div_le (a b : ℚ) : bitSize (a / b) ≤ bitSize a + bitSize b := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [div_zero, bitSize_zero]; unfold bitSize; omega
  have hbn : b.num ≠ 0 := Rat.num_ne_zero.2 hb
  have hQ : ((a.den : ℤ) * b.num) ≠ 0 := mul_ne_zero (by exact_mod_cast a.den_nz) hbn
  have e : a / b = ((a.num * b.den : ℤ) : ℚ) / ((a.den * b.num : ℤ) : ℚ) := by
    have ha : (a.num : ℚ) = a * a.den := (Rat.mul_den_eq_num a).symm
    have hb' : (b.num : ℚ) = b * b.den := (Rat.mul_den_eq_num b).symm
    have h1 : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
    have h2 : (b.den : ℚ) ≠ 0 := by exact_mod_cast b.den_nz
    push_cast
    rw [ha, hb']
    field_simp
  rw [e]
  refine (bitSize_intdiv_le _ _ hQ).trans ?_
  have h1 : (a.num * (b.den : ℤ)).natAbs = a.num.natAbs * b.den := by simp [Int.natAbs_mul]
  have h2 : ((a.den : ℤ) * b.num).natAbs = a.den * b.num.natAbs := by simp [Int.natAbs_mul]
  rw [h1, h2]
  have s3 := size_mul_le' a.num.natAbs b.den
  have s5 := size_mul_le' a.den b.num.natAbs
  unfold bitSize; omega

/-- Bound on the bit size of every kernel direction (polynomial in the input size). -/
def Bd (I : ℕ) : ℕ :=
  2 * (I + 2 + 2 * (I * (I * (I + 3))) + I * I + 2 * (I * (I * (I + 3)) * I)) + 1

theorem findSolution_dir {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x y : Fin m → ℚ) (h : findSolutionV u T x = some y) :
    ∃ d, kernelDirV (sysRows u T) = some d ∧ ∀ j, y j = x j + d j := by
  unfold findSolutionV at h
  rcases hk : kernelDirV (sysRows u T) with _ | d
  · have hk' : kernelDirV ((List.finRange n).map (urowV u) ++ (List.finRange m).filterMap
        fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none) = none := hk
    simp [hk'] at h
  · have hk' : kernelDirV ((List.finRange n).map (urowV u) ++ (List.finRange m).filterMap
        fun j => if j ∈ T then some (Pi.single j (1 : ℚ)) else none) = some d := hk
    simp only [hk', Option.some.injEq] at h
    subst h
    exact ⟨d, rfl, fun j => getD_map_finRange (fun j => x j + d j) j⟩

theorem dir_bound {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (d : Fin m → ℚ)
    (hk : kernelDirV (sysRows u T) = some d) (j : Fin m) : bitSize (d j) ≤ Bd (inputSize u) := by
  have h1 := kernelDirV_bound _ d hk j
  have h2 := bst_le m (Kb (sysRows u T))
  have hnm : n + m ≤ inputSize u := by unfold inputSize; omega
  have h3 : Kb (sysRows u T) ≤ inputSize u * (inputSize u * (inputSize u + 3)) := by
    have := kb_le (sysRows u T) (inputSize u + 3) (sysRows_entry u T)
    have hl := sysRows_len u T
    exact this.trans (Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) le_rfl))
  have h4 : Kb (sysRows u T) * m ≤ inputSize u * (inputSize u * (inputSize u + 3)) * inputSize u :=
    Nat.mul_le_mul h3 (by omega)
  have h5 : m * m ≤ inputSize u * inputSize u := Nat.mul_le_mul (by omega) (by omega)
  unfold Bd; omega

/-- The history of a reachable state: `x = 1/2 + Σ c_i D_i`, the `D_i` kernel directions with
`D_l (J i) = 0` for `i < l` and `D_i (J i) ≠ 0`, and `x (J i) ∈ {0, 1}`. -/
def RCore {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) : Prop :=
  ∃ (k : ℕ) (D : ℕ → Fin m → ℚ) (J : ℕ → Fin m) (c : ℕ → ℚ),
    (∀ i < k, ∀ j, bitSize (D i j) ≤ Bd (inputSize u)) ∧
    (∀ i < k, J i ∈ T) ∧
    (∀ i l, i < l → l < k → D l (J i) = 0) ∧
    (∀ i < k, D i (J i) ≠ 0) ∧
    (∀ i < k, x (J i) = 0 ∨ x (J i) = 1) ∧
    (∀ j, x j = 1 / 2 + ∑ i ∈ Finset.range k, c i * D i j)

def RInv {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ) : Prop :=
  x = (fun _ => 1 / 2) ∨ RCore u T x

theorem rinv_step {n m : ℕ} (u : Fin n → Fin m → ℚ) (T T' : Finset (Fin m)) (x x' : Fin m → ℚ)
    (h : RInv u T x) (hs : loopStepV u T x = some (T', x')) : RInv u T' x' := by
  unfold loopStepV at hs
  rcases hfs : findSolutionV u T x with _ | y
  · simp [hfs] at hs
  simp only [hfs] at hs
  rcases hb : (List.finRange m).foldl (Fv x y) none with _ | ⟨js, g⟩
  · simp [hb] at hs
  simp only [hb, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨hT, hx'⟩ := hs
  obtain ⟨d, hk, hyd⟩ := findSolution_dir u T x y hfs
  have hx'j : ∀ j, x' j = x j + g * d j := by
    intro j; rw [← hx']; simp only [getD_map_finRange]; rw [hyd j]; ring
  have hfix := findSolution_fix u T x y hfs
  have hd0 : ∀ j ∈ T, d j = 0 := by
    intro j hj; have := hfix j hj; rw [hyd j] at this; linarith
  obtain ⟨hjs, hg, -⟩ := fold_spec x y js g hb
  have hdjs : d js ≠ 0 := by intro h0; apply hjs; rw [hyd js, h0, add_zero]
  have hxy : x' js = x js + g * (y js - x js) := by rw [hx'j, hyd js]; ring
  have hx'js : x' js = 0 ∨ x' js = 1 := by
    rcases lt_or_gt_of_ne hjs with hlt | hgt
    · left
      have h1 := gam_down x y js hlt
      rw [hxy, hg]
      linear_combination -h1
    · right
      have h1 := gam_up x y js hgt
      rw [hxy, hg]
      linear_combination h1
  obtain ⟨k, D, J, c, hB, hJT, htri, hdiag, h01, hrep⟩ : RCore u T x := by
    rcases h with h | h
    · refine ⟨0, fun _ _ => 0, fun _ => js, fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i l _ hl => absurd hl (Nat.not_lt_zero _),
        fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _),
        fun j => ?_⟩
      rw [h]; simp
    · exact h
  right
  refine ⟨k + 1, fun i => if i = k then d else D i, fun i => if i = k then js else J i,
    fun i => if i = k then g else c i, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> beta_reduce
  · intro i hi j
    by_cases hik : i = k
    · rw [if_pos hik]; exact dir_bound u T d hk j
    · rw [if_neg hik]; exact hB i (by omega) j
  · intro i hi
    rw [← hT]
    by_cases hik : i = k
    · rw [if_pos hik]; exact Finset.mem_insert_self _ _
    · rw [if_neg hik]; exact Finset.mem_insert_of_mem (hJT i (by omega))
  · intro i l hil hl
    have hik : i ≠ k := by omega
    by_cases hlk : l = k
    · rw [if_pos hlk, if_neg hik]; exact hd0 _ (hJT i (by omega))
    · rw [if_neg hlk, if_neg hik]; exact htri i l hil (by omega)
  · intro i hi
    by_cases hik : i = k
    · rw [if_pos hik, if_pos hik]; exact hdjs
    · rw [if_neg hik, if_neg hik]; exact hdiag i (by omega)
  · intro i hi
    by_cases hik : i = k
    · rw [if_pos hik]; exact hx'js
    · rw [if_neg hik, hx'j, hd0 _ (hJT i (by omega)), mul_zero, add_zero]
      exact h01 i (by omega)
  · intro j
    rw [Finset.sum_range_succ, hx'j, hrep j, if_pos rfl, if_pos rfl]
    have hs : ∑ i ∈ Finset.range k, (if i = k then g else c i) * (if i = k then d else D i) j =
        ∑ i ∈ Finset.range k, c i * D i j := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hik : i ≠ k := by simp at hi; omega
      rw [if_neg hik, if_neg hik]
    rw [hs]; ring

theorem reach_rinv {n m : ℕ} (u : Fin n → Fin m → ℚ) {p : Finset (Fin m) × (Fin m → ℚ)}
    (h : Reachable u p) : RInv u p.1 p.2 := by
  induction h with
  | init => exact Or.inl rfl
  | @step T T' x x' _ hs ih =>
    exact rinv_step u T T' x x' ih (by rw [← val_loopStep u T x 0]; exact hs)

/-- Bit bound for reachable states, as a function of the input size `I` and `B = Bd I`. -/
def XBf (I B : ℕ) : ℕ :=
  2 * ((I + 2) + (2 * (I * (I * B)) + 1) + I * I + (2 * (I * (I * B)) + 1) * I + 1) + 1

theorem core_bound {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ)
    (h : RCore u T x) (j : Fin m) : bitSize (x j) ≤ XBf (inputSize u) (Bd (inputSize u)) := by
  obtain ⟨k, D, J, c, hB, hJT, htri, hdiag, h01, hrep⟩ := h
  have hinj : Function.Injective (fun a : Fin k => J a) := by
    intro a b hab
    have hab' : J a = J b := hab
    by_contra hne
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have := htri a b hlt b.2
      rw [hab'] at this
      exact hdiag b b.2 this
    · have := htri b a hlt a.2
      rw [← hab'] at this
      exact hdiag a a.2 this
  have hkm : k ≤ m := by simpa using Fintype.card_le_of_injective _ hinj
  set I := inputSize u with hI
  have hnm : n + m ≤ I := by rw [hI]; unfold inputSize; omega
  -- the triangular system
  set M : Matrix (Fin k) (Fin k) ℚ := Matrix.of fun a b => D b (J a) with hM
  set e : Fin k → ℚ := fun a => x (J a) - 1 / 2 with he
  have hMc : M.mulVec (fun b => c b) = e := by
    funext a
    simp only [Matrix.mulVec, dotProduct, hM, Matrix.of_apply, he]
    rw [hrep (J a), Finset.sum_range (fun i => c i * D i (J a)), add_sub_cancel_left]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)
  have hdet : M.det ≠ 0 := by
    have hbt : M.IsLowerTriangular := by
      intro a b hab
      have hab' : a < b := OrderDual.toDual_lt_toDual.1 hab
      simp only [hM, Matrix.of_apply]
      exact htri a b hab' b.2
    rw [Matrix.det_of_isLowerTriangular M hbt]
    exact Finset.prod_ne_zero_iff.2 (fun a _ => hdiag a a.2)
  have hcr : ∀ b : Fin k, M.det * c b = (M.updateCol b e).det := by
    intro b
    have h1 : M.det • (fun b : Fin k => c b) = Matrix.cramer M e := by
      rw [Matrix.cramer_eq_adjugate_mulVec, ← hMc, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
        Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 := congrFun h1 b
    rw [Matrix.cramer_apply] at h2
    simpa using h2
  -- integer scaling
  set rows : List (Fin m → ℚ) := (List.range k).map D with hrows
  have hmem : ∀ i < k, D i ∈ rows := fun i hi => List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  set K := Kb rows with hK
  have hKl : K ≤ k * (m * Bd I) := by
    have := kb_le rows (Bd I) (by
      intro r hr c'
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hr
      exact hB i (List.mem_range.1 hi) c')
    simpa [hrows] using this
  set Dn' : ℕ := Dn rows with hDn
  have hDpos : 0 < Dn' := dn_pos rows
  have hDle : Dn' ≤ 2 ^ K := dn_le rows
  set Wn : ℕ := 2 * 2 ^ (2 * K) with hWn
  have hDW : Dn' ≤ Wn := by
    have : 2 ^ K ≤ 2 ^ (2 * K) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hsc : ∀ i < k, ∀ c' : Fin m, ∃ z : ℤ, (2 * Dn' : ℚ) * D i c' = z ∧ |z| ≤ (Wn : ℤ) := by
    intro i hi c'
    obtain ⟨z, hz, hzb⟩ := scaled_int (hmem i hi) c'
    refine ⟨2 * z, ?_, ?_⟩
    · rw [mul_assoc, hz]; push_cast; ring
    · rw [abs_mul]; push_cast; simp only [abs_two]; linarith
  have hscM : ∀ a b : Fin k, ∃ z : ℤ, (2 * Dn' : ℚ) * M a b = z ∧ |z| ≤ (Wn : ℤ) :=
    fun a b => hsc b b.2 (J a)
  have hscE : ∀ b : Fin k, ∀ a b' : Fin k,
      ∃ z : ℤ, (2 * Dn' : ℚ) * M.updateCol b e a b' = z ∧ |z| ≤ (Wn : ℤ) := by
    intro b a b'
    rw [Matrix.updateCol_apply]
    split_ifs
    · rcases h01 a a.2 with h0 | h0
      · refine ⟨-(Dn' : ℤ), ?_, ?_⟩
        · simp only [he, h0]; push_cast; ring
        · rw [abs_neg, abs_of_nonneg (by positivity)]; exact_mod_cast hDW
      · refine ⟨(Dn' : ℤ), ?_, ?_⟩
        · simp only [he, h0]; push_cast; ring
        · rw [abs_of_nonneg (by positivity)]; exact_mod_cast hDW
    · exact hscM a b'
  obtain ⟨z0, hz0, hz0b⟩ := det_int_bound M (2 * Dn' : ℚ) (Wn : ℤ) hscM
  choose zb hzb hzbb using fun b : Fin k => det_int_bound (M.updateCol b e) (2 * Dn' : ℚ) (Wn : ℤ) (hscE b)
  choose w hw hwb using fun b : Fin k => hsc b b.2 j
  set Fn : ℕ := k.factorial * Wn ^ k with hFn
  have hF : ((k.factorial : ℤ) * (Wn : ℤ) ^ k) = (Fn : ℤ) := by rw [hFn]; push_cast; ring
  rw [hF] at hz0b hzbb
  have hz0ne : z0 ≠ 0 := by
    intro h0
    rw [h0] at hz0
    have : (2 * Dn' : ℚ) ^ k ≠ 0 := by positivity
    exact (mul_ne_zero this hdet) (by exact_mod_cast hz0)
  -- the formula for x j
  have hxj : x j = ((Dn' * z0 + ∑ b : Fin k, w b * zb b : ℤ) : ℚ) / ((2 * Dn' * z0 : ℤ) : ℚ) := by
    have hQ : ((2 * Dn' * z0 : ℤ) : ℚ) ≠ 0 := by
      have : (2 * (Dn' : ℤ) * z0) ≠ 0 := mul_ne_zero (by positivity) hz0ne
      exact_mod_cast this
    rw [eq_div_iff hQ]
    push_cast
    have hsum : ∀ b : Fin k, (w b : ℚ) * (zb b : ℚ) =
        (2 * Dn' : ℚ) ^ k * (2 * Dn' : ℚ) * (D b j * (M.det * c b)) := by
      intro b
      rw [← hw b, ← hzb b, ← hcr b]; ring
    rw [Finset.sum_congr rfl (fun b _ => hsum b), ← Finset.mul_sum, ← hz0, hrep j,
      Finset.sum_range (fun i => c i * D i j)]
    have : ∑ b : Fin k, D b j * (M.det * c b) = M.det * ∑ b : Fin k, c b * D b j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun b _ => by ring)
    rw [this]; ring
  -- bounds
  have hW0 : (0 : ℤ) ≤ Wn := by positivity
  have hF0 : (0 : ℤ) ≤ Fn := by positivity
  have hS : |∑ b : Fin k, w b * zb b| ≤ k * ((Wn : ℤ) * Fn) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hle : ∀ b ∈ (Finset.univ : Finset (Fin k)), |w b * zb b| ≤ (Wn : ℤ) * Fn := by
      intro b _
      rw [abs_mul]; exact mul_le_mul (hwb b) (hzbb b) (abs_nonneg _) hW0
    have := Finset.sum_le_card_nsmul Finset.univ _ _ hle
    simpa using this
  set Bn : ℕ := (k + 2) * Wn * Fn with hBn
  have hDWz : (Dn' : ℤ) ≤ Wn := by exact_mod_cast hDW
  have hN : |(Dn' : ℤ) * z0 + ∑ b : Fin k, w b * zb b| ≤ (Bn : ℤ) := by
    have h1 : |(Dn' : ℤ) * z0| ≤ (Wn : ℤ) * Fn := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul hDWz hz0b (abs_nonneg _) hW0
    have h2 := abs_add_le ((Dn' : ℤ) * z0) (∑ b : Fin k, w b * zb b)
    have h3 : (Bn : ℤ) = (k + 2) * ((Wn : ℤ) * Fn) := by rw [hBn]; push_cast; ring
    have e : ((k : ℤ) + 2) * ((Wn : ℤ) * Fn) = k * ((Wn : ℤ) * Fn) + 2 * ((Wn : ℤ) * Fn) := by ring
    have h4 : (0 : ℤ) ≤ (Wn : ℤ) * Fn := mul_nonneg hW0 hF0
    rw [h3, e]; linarith
  have hQb : |2 * (Dn' : ℤ) * z0| ≤ (Bn : ℤ) := by
    have h3 : (Bn : ℤ) = (k + 2) * ((Wn : ℤ) * Fn) := by rw [hBn]; push_cast; ring
    have h4 : (0 : ℤ) ≤ (Wn : ℤ) * Fn := mul_nonneg hW0 hF0
    have h1 : |(Dn' : ℤ) * z0| ≤ (Wn : ℤ) * Fn := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul hDWz hz0b (abs_nonneg _) hW0
    have e : ((k : ℤ) + 2) * ((Wn : ℤ) * Fn) = k * ((Wn : ℤ) * Fn) + 2 * ((Wn : ℤ) * Fn) := by ring
    have h5 : (0 : ℤ) ≤ k * ((Wn : ℤ) * Fn) := by positivity
    rw [mul_assoc, abs_mul, h3, e, abs_two]; linarith
  have hbit := bitSize_frac_le _ _ (mul_ne_zero (mul_ne_zero two_ne_zero (by positivity)) hz0ne)
    Bn hN hQb
  rw [hxj]
  refine hbit.trans ?_
  -- size of Bn
  have hf : k.factorial ≤ (2 ^ k) ^ k :=
    (Nat.factorial_le_pow k).trans (Nat.pow_le_pow_left (two_pow_gt k).le k)
  have hBn2 : Bn ≤ 2 ^ ((k + 2) + (2 * K + 1) + k * k + (2 * K + 1) * k) := by
    have e : (2 : ℕ) ^ ((k + 2) + (2 * K + 1) + k * k + (2 * K + 1) * k) =
        2 ^ (k + 2) * 2 ^ (2 * K + 1) * ((2 ^ k) ^ k * (2 ^ (2 * K + 1)) ^ k) := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add, ← pow_add]
      congr 1; ring
    have eW : Wn = 2 ^ (2 * K + 1) := by rw [hWn, pow_succ]; ring
    rw [e, hBn, hFn, eW]
    exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (two_pow_gt _).le) (Nat.mul_le_mul_right _ hf)
  have hsz : Nat.size Bn ≤ (k + 2) + (2 * K + 1) + k * k + (2 * K + 1) * k + 1 := by
    rw [Nat.size_le, pow_succ]
    have : 0 < 2 ^ ((k + 2) + (2 * K + 1) + k * k + (2 * K + 1) * k) := by positivity
    omega
  have hkI : k ≤ I := by omega
  have hK2 : K ≤ I * (I * Bd I) :=
    hKl.trans (Nat.mul_le_mul hkI (Nat.mul_le_mul (by omega) le_rfl))
  have hkk : k * k ≤ I * I := Nat.mul_le_mul hkI hkI
  have hKk : (2 * K + 1) * k ≤ (2 * (I * (I * Bd I)) + 1) * I := Nat.mul_le_mul (by omega) hkI
  unfold XBf; omega

theorem reach_bound {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ)
    (h : Reachable u (T, x)) (j : Fin m) :
    bitSize (x j) ≤ XBf (inputSize u) (Bd (inputSize u)) := by
  rcases reach_rinv u h with h0 | h0
  · have hx : x j = 1 / 2 := by
      have := congrFun h0 j
      simpa using this
    rw [hx]
    have : bitSize (1 / 2 : ℚ) = 4 := by unfold bitSize; norm_num; rfl
    rw [this]; unfold XBf; omega
  · exact core_bound u T x h0 j

theorem gam_bound {m : ℕ} (x y : Fin m → ℚ) (j : Fin m) :
    bitSize (gam x y j) ≤ bitSize (1 - x j) + bitSize (y j - x j) + bitSize (x j) +
      bitSize (x j - y j) := by
  unfold gam
  split_ifs
  · have := bitSize_div_le (1 - x j) (y j - x j); omega
  · have := bitSize_div_le (x j) (x j - y j); omega

theorem fold_acc_bound {m : ℕ} (x y : Fin m → ℚ) (G : ℕ) (hG : ∀ j, bitSize (gam x y j) ≤ G) :
    ∀ (l : List (Fin m)) (acc : Option (Fin m × ℚ)), (∀ p, acc = some p → bitSize p.2 ≤ G) →
      ∀ p, l.foldl (Fv x y) acc = some p → bitSize p.2 ≤ G
  | [], acc, h => h
  | j :: l, acc, h => fold_acc_bound x y G hG l (Fv x y acc j) (by
      intro p hp
      unfold Fv at hp
      split at hp
      · exact h p hp
      · split at hp
        · rw [← Option.some.inj hp]; exact hG j
        · split at hp
          · rw [← Option.some.inj hp]; exact hG j
          · exact h p hp)

theorem cost_loopStep {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ)
    (Xb : ℕ) (hx : ∀ j, bitSize (x j) ≤ Xb) :
    Cost (loopStep u T x) (200 * 100 ^ 5 * (inputSize u + ∑ j, bitSize (x j) + 1) ^ 20 +
      (m * (1 + 6 * (2 * (20 * (Xb + Bd (inputSize u) + 1)) + 1) ^ 2) +
        m * (1 + 4 * (2 * (20 * (Xb + Bd (inputSize u) + 1)) + 1) ^ 2))) := by
  set B := Bd (inputSize u) with hBd
  set Y := 20 * (Xb + B + 1) with hY
  set O := (2 * Y + 1) ^ 2 with hO
  have hop : ∀ a b : ℚ, bitSize a ≤ Y → bitSize b ≤ Y → opCost a b ≤ O := by
    intro a b ha hb
    unfold opCost
    exact Nat.pow_le_pow_left (by omega) 2
  unfold loopStep
  refine cost_bind (cost_poly u T x) (val_findSolution u T x) ?_
  rcases hfs : findSolutionV u T x with _ | y
  · exact cost_mono (cost_pure _) (Nat.zero_le _)
  obtain ⟨d, hk, hyd⟩ := findSolution_dir u T x y hfs
  have hd : ∀ j, bitSize (d j) ≤ B := fun j => dir_bound u T d hk j
  have hyb : ∀ j, bitSize (y j) ≤ 2 * (Xb + B) := by
    intro j; rw [hyd j]; have := bitSize_add_le (x j) (d j); have := hx j; have := hd j; omega
  have h1x : ∀ j, bitSize (1 - x j) ≤ 2 * (3 + Xb) := by
    intro j; have := bitSize_sub_le 1 (x j); have := hx j; rw [bitSize_one] at *; omega
  have hyx : ∀ j, bitSize (y j - x j) ≤ 2 * (2 * (Xb + B) + Xb) := by
    intro j; have := bitSize_sub_le (y j) (x j); have := hx j; have := hyb j; omega
  have hxy : ∀ j, bitSize (x j - y j) ≤ 2 * (2 * (Xb + B) + Xb) := by
    intro j; have := bitSize_sub_le (x j) (y j); have := hx j; have := hyb j; omega
  have hq1 : ∀ j, bitSize ((1 - x j) / (y j - x j)) ≤ Y := by
    intro j; have := bitSize_div_le (1 - x j) (y j - x j); have := h1x j; have := hyx j; omega
  have hq2 : ∀ j, bitSize (x j / (x j - y j)) ≤ Y := by
    intro j; have := bitSize_div_le (x j) (x j - y j); have := hx j; have := hxy j; omega
  set G := 8 * Xb + 4 * B + 6 with hG
  have hgam : ∀ j, bitSize (gam x y j) ≤ G := by
    intro j
    unfold gam
    split_ifs
    · have := bitSize_div_le (1 - x j) (y j - x j); have := h1x j; have := hyx j; omega
    · have := bitSize_div_le (x j) (x j - y j); have := hx j; have := hxy j; omega
  have hxY : ∀ j, bitSize (x j) ≤ Y := fun j => by have := hx j; omega
  have hyY : ∀ j, bitSize (y j) ≤ Y := fun j => by have := hyb j; omega
  have h1xY : ∀ j, bitSize (1 - x j) ≤ Y := fun j => by have := h1x j; omega
  have hyxY : ∀ j, bitSize (y j - x j) ≤ Y := fun j => by have := hyx j; omega
  have hxyY : ∀ j, bitSize (x j - y j) ≤ Y := fun j => by have := hxy j; omega
  have hGY : G ≤ Y := by omega
  dsimp only
  refine cost_bind (c1 := m * (1 + 6 * O)) (cost_mono (cost_foldlM _ (Fv x y) ?hv (1 + 6 * O)
    (List.finRange m) none ?hc) (by rw [List.length_finRange])) (val_foldlM _ (Fv x y) ?hv _ _) ?hk
  case hv =>
    intro acc j
    refine val_bind (val_tick _) (val_bind (val_qeq _ _) ?_)
    unfold Fv
    cases decide (y j = x j)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine val_bind (val_qlt _ _) ?_
      have hm : ∀ g : ℚ, Val (match acc with
          | none => pure (some (j, g))
          | some (_, g0) => do
            let lt ← qlt g g0
            pure (if lt then some (j, g) else acc) : StateM ℕ (Option (Fin m × ℚ)))
          (match acc with
          | none => some (j, g)
          | some (_, g0) => if decide (g < g0) = true then some (j, g) else acc) := by
        intro g
        cases acc with
        | none => exact val_pure _
        | some pr =>
          obtain ⟨j0, g0⟩ := pr
          exact val_bind (val_qlt _ _) (val_pure _)
      unfold gam
      cases decide (x j < y j)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact val_bind (val_qsub _ _) (val_bind (val_qdiv _ _) (hm _))
      · simp only [↓reduceIte]
        exact val_bind (val_qsub _ _) (val_bind (val_qsub _ _) (val_bind (val_qdiv _ _) (hm _)))
    · simp only [↓reduceIte]
      exact val_pure _
  case hc =>
    intro i hi
    have hacc := fold_acc_bound x y G hgam ((List.finRange m).take i) none
      (fun p hp => by cases hp)
    generalize ((List.finRange m).take i).foldl (Fv x y) none = acc at hacc ⊢
    generalize (List.finRange m)[i] = j
    refine cost_mono (cost_bind (c1 := 1) (c2 := O + 5 * O) (cost_tick 1) (val_tick _) ?_)
      (by omega)
    refine cost_bind (c1 := O) (c2 := 5 * O) (cost_mono (cost_qeq _ _) (hop _ _ (hyY j) (hxY j)))
      (val_qeq _ _) ?_
    cases decide (y j = x j)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine cost_mono (cost_bind (c1 := O) (c2 := 4 * O)
        (cost_mono (cost_qlt _ _) (hop _ _ (hxY j) (hyY j))) (val_qlt _ _) ?_) (by omega)
      have hm : ∀ g : ℚ, bitSize g ≤ Y → ∀ acc' : Option (Fin m × ℚ),
          (∀ p, acc' = some p → bitSize p.2 ≤ G) → Cost (match acc' with
          | none => pure (some (j, g))
          | some (_, g0) => do
            let lt ← qlt g g0
            pure (if lt then some (j, g) else acc') : StateM ℕ (Option (Fin m × ℚ))) O := by
        intro g hg acc' hacc'
        cases acc' with
        | none => exact cost_mono (cost_pure _) (Nat.zero_le _)
        | some pr =>
          obtain ⟨j0, g0⟩ := pr
          have h0 : bitSize g0 ≤ G := hacc' _ rfl
          exact cost_mono (cost_bind (c2 := 0) (cost_mono (cost_qlt _ _) (hop _ _ hg (by omega)))
            (val_qlt _ _) (cost_pure _)) (by omega)
      cases decide (x j < y j)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact cost_mono (cost_bind (c1 := O) (c2 := O + O)
          (cost_mono (cost_qsub _ _) (hop _ _ (hxY j) (hyY j))) (val_qsub _ _)
          (cost_bind (c1 := O) (c2 := O) (cost_mono (cost_qdiv _ _) (hop _ _ (hxY j) (hxyY j)))
            (val_qdiv _ _) (hm _ (hq2 j) acc hacc))) (by omega)
      · simp only [↓reduceIte]
        have h1 : bitSize (1 : ℚ) ≤ Y := by rw [bitSize_one]; omega
        exact cost_mono (cost_bind (c1 := O) (c2 := O + (O + O))
          (cost_mono (cost_qsub _ _) (hop _ _ h1 (hxY j))) (val_qsub _ _)
          (cost_bind (c1 := O) (c2 := O + O) (cost_mono (cost_qsub _ _) (hop _ _ (hyY j) (hxY j)))
            (val_qsub _ _)
            (cost_bind (c1 := O) (c2 := O) (cost_mono (cost_qdiv _ _) (hop _ _ (h1xY j) (hyxY j)))
              (val_qdiv _ _) (hm _ (hq1 j) acc hacc)))) (by omega)
    · simp only [↓reduceIte]
      exact cost_mono (cost_pure _) (Nat.zero_le _)
  case hk =>
    rcases hb : (List.finRange m).foldl (Fv x y) none with _ | ⟨js, g⟩
    · exact cost_mono (cost_pure _) (Nat.zero_le _)
    dsimp only
    have hg : bitSize g ≤ G := fold_acc_bound x y G hgam _ none (fun p hp => by cases hp) _ hb
    have hgY : bitSize g ≤ Y := by omega
    have h1 : bitSize (1 : ℚ) ≤ Y := by rw [bitSize_one]; omega
    have h1g : bitSize (1 - g) ≤ Y := by
      have := bitSize_sub_le 1 g; rw [bitSize_one] at this; omega
    have h1gx : ∀ j, bitSize ((1 - g) * x j) ≤ Y := by
      intro j; have := bitSize_mul_le (1 - g) (x j); have := bitSize_sub_le 1 g
      rw [bitSize_one] at this; have := hx j; omega
    have hgy : ∀ j, bitSize (g * y j) ≤ Y := by
      intro j; have := bitSize_mul_le g (y j); have := hyb j; omega
    refine cost_mono (cost_bind (c2 := 0) (cost_mapM _ (fun j => (1 - g) * x j + g * y j)
      (fun j => val_bind (val_tick _) (val_bind (val_qsub _ _) (val_bind (val_qmul _ _)
        (val_bind (val_qmul _ _) (val_qadd _ _))))) (1 + 4 * O) _ (fun j _ => ?_))
      (val_mapM _ _ (fun j => val_bind (val_tick _) (val_bind (val_qsub _ _) (val_bind (val_qmul _ _)
        (val_bind (val_qmul _ _) (val_qadd _ _))))) _) (cost_pure _))
      (by rw [List.length_finRange]; omega)
    exact cost_mono (cost_bind (c1 := 1) (c2 := O + (O + (O + O))) (cost_tick 1) (val_tick _)
      (cost_bind (c1 := O) (c2 := O + (O + O)) (cost_mono (cost_qsub _ _) (hop _ _ h1 hgY))
        (val_qsub _ _)
        (cost_bind (c1 := O) (c2 := O + O) (cost_mono (cost_qmul _ _) (hop _ _ h1g (hxY j)))
          (val_qmul _ _)
          (cost_bind (c1 := O) (c2 := O) (cost_mono (cost_qmul _ _) (hop _ _ hgY (hyY j)))
            (val_qmul _ _) (cost_mono (cost_qadd _ _) (hop _ _ (h1gx j) (hgy j))))))) (by omega)

theorem bd_le (I : ℕ) : Bd I ≤ 50 * (I + 1) ^ 4 := by
  set b := I + 1 with hb
  have hI : I ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have h0 : Bd I ≤ 2 * (b + 2 + 2 * (b * (b * (b + 3))) + b * b + 2 * (b * (b * (b + 3)) * b)) + 1 := by
    unfold Bd; gcongr
  have p1 : b ≤ b ^ 4 := Nat.le_self_pow (by norm_num) b
  have p2 : b ^ 2 ≤ b ^ 4 := Nat.pow_le_pow_right hb1 (by norm_num)
  have p3 : b ^ 3 ≤ b ^ 4 := Nat.pow_le_pow_right hb1 (by norm_num)
  have p0 : 1 ≤ b ^ 4 := Nat.one_le_pow _ _ hb1
  refine h0.trans ?_
  ring_nf; omega

theorem xb_le (I : ℕ) : XBf I (Bd I) ≤ 500 * (I + 1) ^ 7 := by
  set b := I + 1 with hb
  have hI : I ≤ b := by omega
  have hb1 : 1 ≤ b := by omega
  have hB := bd_le I
  rw [← hb] at hB
  have h0 : XBf I (Bd I) ≤ XBf b (50 * b ^ 4) := by
    unfold XBf; gcongr
  have p1 : b ≤ b ^ 7 := Nat.le_self_pow (by norm_num) b
  have p2 : b ^ 2 ≤ b ^ 7 := Nat.pow_le_pow_right hb1 (by norm_num)
  have p6 : b ^ 6 ≤ b ^ 7 := Nat.pow_le_pow_right hb1 (by norm_num)
  have p0 : 1 ≤ b ^ 7 := Nat.one_le_pow _ _ hb1
  refine h0.trans ?_
  unfold XBf
  ring_nf; omega

def CC : ℕ := 200 * 100 ^ 5 * 501 ^ 20 + 2 + 10 * 22041 ^ 2 + 500

theorem final_bound {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ)
    (hr : Reachable u (T, x)) :
    (∀ j, bitSize (x j) ≤ CC * ((inputSize u + 1) ^ 8) ^ 20) ∧
    ∀ t, ((loopStep u T x).run t).2 ≤ t + CC * ((inputSize u + 1) ^ 8) ^ 20 := by
  have hX : ∀ j, bitSize (x j) ≤ 500 * (inputSize u + 1) ^ 7 :=
    fun j => (reach_bound u T x hr j).trans (xb_le (inputSize u))
  have hc := cost_loopStep u T x _ hX
  have hB := bd_le (inputSize u)
  have hnm : n + m ≤ inputSize u := by unfold inputSize; omega
  have hsum : ∑ j, bitSize (x j) ≤ m * (500 * (inputSize u + 1) ^ 7) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => bitSize (x j)) _ (fun j _ => hX j)
    simpa using this
  generalize ∑ j, bitSize (x j) = S at hc hsum
  generalize Bd (inputSize u) = B at hc hB
  generalize inputSize u = I at hc hB hX hnm hsum ⊢
  generalize hb : I + 1 = b at hc hB hX hsum ⊢
  have hb1 : 1 ≤ b := by omega
  have hm : m ≤ b := by omega
  have p47 : b ^ 4 ≤ b ^ 7 := Nat.pow_le_pow_right hb1 (by norm_num)
  have p78 : b ^ 7 ≤ b ^ 8 := Nat.pow_le_pow_right hb1 (by norm_num)
  have p18 : b ≤ b ^ 8 := Nat.le_self_pow (by norm_num) b
  have q7 : 1 ≤ b ^ 7 := Nat.one_le_pow _ _ hb1
  have hbb : b * b ^ 7 = b ^ 8 := (pow_succ' b 7).symm
  have hS1 : m * (500 * b ^ 7) ≤ 500 * b ^ 8 := by
    calc m * (500 * b ^ 7) ≤ b * (500 * b ^ 7) := Nat.mul_le_mul_right _ hm
      _ = 500 * (b * b ^ 7) := Nat.mul_left_comm _ _ _
      _ = 500 * b ^ 8 := by rw [hbb]
  have hS8 : I + S + 1 ≤ 501 * b ^ 8 := by omega
  have hY : 2 * (20 * (500 * b ^ 7 + B + 1)) + 1 ≤ 22041 * b ^ 8 := by omega
  have hX8 : ∀ j, bitSize (x j) ≤ 500 * b ^ 8 := fun j => (hX j).trans (by omega)
  generalize b ^ 8 = P at hS8 hY hX8 p18
  have hP1 : 1 ≤ P := by omega
  have hPP : P ≤ P ^ 20 := Nat.le_self_pow (by norm_num) P
  have hP3 : P ^ 3 ≤ P ^ 20 := Nat.pow_le_pow_right hP1 (by norm_num)
  have hCC1 : 500 ≤ CC := by unfold CC; norm_num
  refine ⟨fun j => (hX8 j).trans (Nat.mul_le_mul hCC1 hPP), fun t => (hc t).trans ?_⟩
  refine Nat.add_le_add_left ?_ t
  have hFS : 200 * 100 ^ 5 * (I + S + 1) ^ 20 ≤ 200 * 100 ^ 5 * (501 ^ 20 * P ^ 20) := by
    have := Nat.mul_le_mul_left (200 * 100 ^ 5) (Nat.pow_le_pow_left hS8 20)
    rw [mul_pow] at this
    exact this
  have hQ : (2 * (20 * (500 * b ^ 7 + B + 1)) + 1) ^ 2 ≤ 22041 ^ 2 * P ^ 2 := by
    have := Nat.pow_le_pow_left hY 2
    rw [mul_pow] at this
    exact this
  generalize (2 * (20 * (500 * b ^ 7 + B + 1)) + 1) ^ 2 = Q at hQ ⊢
  generalize hK2 : (22041 : ℕ) ^ 2 = K2 at hQ ⊢
  have hR : m * (1 + 6 * Q) + m * (1 + 4 * Q) ≤ 2 * P ^ 20 + 10 * K2 * P ^ 20 := by
    have e0 : m * (1 + 6 * Q) + m * (1 + 4 * Q) = m * (2 + 10 * Q) := by ring
    have e1 : m * (2 + 10 * Q) ≤ P * (2 + 10 * (K2 * P ^ 2)) :=
      Nat.mul_le_mul (by omega) (Nat.add_le_add_left (Nat.mul_le_mul_left 10 hQ) 2)
    have e2 : P * (2 + 10 * (K2 * P ^ 2)) = 2 * P + 10 * K2 * P ^ 3 := by ring
    rw [e0]
    refine e1.trans ?_
    rw [e2]
    exact Nat.add_le_add (Nat.mul_le_mul_left 2 hPP) (Nat.mul_le_mul_left _ hP3)
  generalize P ^ 20 = Z at hFS hR ⊢
  generalize hP0 : (200 : ℕ) * 100 ^ 5 = P0 at hFS ⊢
  have hCC2 : P0 * 501 ^ 20 + 2 + 10 * K2 ≤ CC := by
    rw [← hK2, ← hP0]; unfold CC; exact Nat.le_add_right _ _
  have e3 : P0 * (501 ^ 20 * Z) + (2 * Z + 10 * K2 * Z) = (P0 * 501 ^ 20 + 2 + 10 * K2) * Z := by ring
  calc P0 * (I + S + 1) ^ 20 + (m * (1 + 6 * Q) + m * (1 + 4 * Q))
      ≤ P0 * (501 ^ 20 * Z) + (2 * Z + 10 * K2 * Z) := Nat.add_le_add hFS hR
    _ = (P0 * 501 ^ 20 + 2 + 10 * K2) * Z := e3
    _ ≤ CC * Z := Nat.mul_le_mul_right _ hCC2

end LSP
end ConsensusHalvingItems.Additive

open ConsensusHalvingItems.Additive in
theorem solution :
    ∃ C k : ℕ, ∀ {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m)) (x : Fin m → ℚ),
      Reachable u (T, x) →
        (∀ j, bitSize (x j) ≤ C * (inputSize u + 1) ^ k) ∧
        ∀ t, ((loopStep u T x).run t).2 ≤ t + C * (inputSize u + 1) ^ k := by
  refine ⟨LSP.CC, 8 * 20, fun {n m} u T x hr => ?_⟩
  rw [pow_mul]
  exact LSP.final_bound u T x hr
